{-# LANGUAGE TemplateHaskell, MultiParamTypeClasses, FlexibleContexts,
NoMonomorphismRestriction, FlexibleInstances, FunctionalDependencies,
GADTs, TypeOperators, DataKinds, KindSignatures, PolyKinds, TypeFamilies, UndecidableInstances, 
AllowAmbiguousTypes, OverlappingInstances, ScopedTypeVariables #-}

import Language.Haskell.TH

import Control.Exception.Base
import Control.Monad
import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as Map




type AttrName = String
type ChildName = Name

data Attr a t = Attr {attrName :: AttrName, attrType :: Type}
data AttrAt n a t
data Child p t = Child ChildName Type

data Proxy a = Proxy

-- | Definition of a synthesised attribute @a@ of type @t@ on the
-- productions in p.
data Syn (ps :: [*]) a t where
    SynNil :: Syn '[] a t
    SynCons :: AGE p a t -> Syn ps a t -> Syn (p ': ps) a t

type family (:++) (xs :: [k]) (ys :: [k]) where
    '[] :++ ys = ys
    (x ': xs) :++ ys = x ': (xs :++ ys)

(<&>) :: Syn ps a t -> Syn qs a t -> Syn (ps :++ qs) a t
SynNil <&> qs = qs
(SynCons p ps) <&> qs = SynCons p (ps <&> qs)

type family Prods n :: [*]

type family Diff (xs :: [*]) (ys :: [*]) where
    Diff xs '[] = xs
    Diff xs (y ': ys) = Diff (Remove xs y) ys

type family Remove (xs :: [*]) (y :: *) where
    Remove '[] y = '[]
    Remove (x ': xs) x = xs
    Remove (x ': xs) y = x ': (Remove xs y)

class HasProds n ps (pps :: ([*],[*]))
instance HasProds n ps '( '[], '[])

type CmpProds n ps = '(Diff (Prods n) ps , Diff ps (Prods n))

data AG dep def where
    AGNil :: AG a '[]
    AGSyn :: (HasProds n ps (CmpProds n ps)) =>
              Proxy n -> Attr a t -> Syn ps as t -> AG as def -> AG as (AttrAt n a t ': def)

-- | Define a synthesised attribute
syn :: (HasProds n ps (CmpProds n ps)) => Proxy n -> Attr a t -> 
       Syn ps as t -> AG as '[AttrAt n a t]
syn n a s = AGSyn n a s AGNil

-- | Combine attribute grammars
(<+>) :: AG dep def1 -> AG dep def2 -> AG dep (def1 :++ def2)
AGNil <+> ag = ag
AGSyn n a s ag1 <+> ag2 = AGSyn n a s (ag1 <+> ag2)

-- | Finds the first duplicate in a type level list if there is any

type family Duplicate (xs :: [k]) where
    Duplicate '[] = '[]
    Duplicate (x ': xs) = HasDupl x xs xs

type family HasDupl (x :: k) (xs :: [k]) (cont :: [k]) where
    HasDupl x '[] cont = Duplicate cont
    HasDupl x (x ': xs) cont = '[x]
    HasDupl x (y ': xs) cont = HasDupl x xs cont

compileAG :: (Duplicate atts ~ '[]) => AG atts atts -> Q [Dec]
compileAG _ = return []


-- | as has an attribute a of type t on a node of type n.
class HasAtt as n a t 

instance HasAtt (AttrAt n a t ': as) n a t
instance HasAtt as n a t => HasAtt (x ': as) n a t

class HasChild con chi ty | chi -> ty, chi -> con

type family ConType con :: *

infix 6 #

-- | Read attribute at a given child

(#) :: (HasChild c p t', HasAtt as n a t) => Attr a t -> Child p n -> AGE c as t
a # (Child child _) = getAttr a (AtChild child)

-- | Read attribute at the root
att :: HasAtt as (ConType c) a t => Attr a t -> AGE c as t
att a = getAttr a AtRoot


-- | Implementation of attribute lookup (this function should be hidden).

getAttr (Attr attN attT) pos = AGE $ StateT $ \env -> 
                       case Map.lookup attN (envAttrs env) of
                         Just (m,ty) -> assert (ty == attT) $
                                        case Map.lookup pos m of
                                          Just n -> return (VarE n, env)
                                          Nothing -> freshVar env m
                         Nothing -> freshVar env Map.empty
  where freshVar env m = do n <- newName attN
                            return (VarE n, env {envAttrs = Map.insert attN 
                                                            (Map.insert pos n m, attT) 
                                                            (envAttrs env)} )


val :: HasChild c p t => Child p t -> AGE c a t
val (Child child chTy) = AGE $ StateT $ \env -> 
                    case Map.lookup child (envVals env) of
                        Just (n,ty) -> assert (ty == chTy) $ return (VarE n, env)
                        Nothing -> do n <- newName "val"
                                      return (VarE n, env {envVals = Map.insert child (n,chTy) 
                                                                     (envVals env)})

root :: AGE c s (ConType c)
root = AGE $ StateT $ \env -> 
       case envRootVal env of
         Just n -> return (VarE n, env)
         Nothing -> do n <- newName "rootval"
                       return (VarE n, env {envRootVal = Just n})

data Pos = AtChild ChildName | AtRoot
         deriving (Eq, Ord)

data Env = Env {envAttrs :: Map AttrName (Map Pos Name, Type)
               ,envVals :: Map ChildName (Name, Type)
               ,envRootVal :: Maybe Name}


-- | Attribute grammar expression (i.e. the right-hand side of a AG
-- rule). t is the type of the root node for which the expression is
-- used. pos lists the positions that are used in the expression. att
-- lists the attributes that are used in the expression. a is the
-- (run-time) type of the expression.

newtype AGE c att a = AGE {unAGE :: StateT Env Q Exp}

infixl <>

(<>) :: AGE c att (a -> b) -> AGE c att a
     -> AGE c att b
(AGE mf) <> (AGE mx) = AGE $ do ex1 <- mf
                                ex2 <- mx
                                return $ AppE ex1 ex2



mkAGESimple :: Q (TExp a) -> AGE c att a
mkAGESimple q = AGE $ StateT $ \ env -> liftM (\e -> (unType e, env)) q


data Nat = Zero | Succ Nat


type family MkAGE (n :: Nat) c att a where
    MkAGE Zero c att a = AGE c att a
    MkAGE (Succ n) c att (a -> b) = AGE c att a -> MkAGE n c att b

data NumArgs :: Nat -> * -> * where
    NAZero :: NumArgs Zero a 
    NASucc :: NumArgs n b -> NumArgs (Succ n) (a -> b)

mkAGE_ :: NumArgs n a -> AGE c att a -> MkAGE n c att a
mkAGE_ NAZero q = q
mkAGE_ (NASucc n) q = \ x -> mkAGE_ n (q <> x)

type family CountArgs (f :: *) :: Nat where 
    CountArgs (a -> b) = Succ (CountArgs b)
    CountArgs result = Zero

class CNumArgs (numArgs :: Nat) (a :: *) where 
    getNA :: NumArgs numArgs a
instance CNumArgs Zero a where
    getNA = NAZero
instance CNumArgs n b => CNumArgs (Succ n) (a -> b) where
    getNA = NASucc getNA


mkAGE :: forall a c att . CNumArgs (CountArgs a) a => Q (TExp a) -> MkAGE (CountArgs a) c att a
mkAGE q = mkAGE_ (getNA :: NumArgs (CountArgs a) a) (mkAGESimple q :: AGE c att a)

mkAGE' :: forall n a c att . NumArgs n a -> Q (TExp a) -> MkAGE n c att a
mkAGE' n q = mkAGE_ n (mkAGESimple q :: AGE c att a)

-- example use of mkAGE


-- Since @min@ is polymorphic (in its result type) we have to use
-- 'mkAGE'' and give the number of arguments explicitly.
min' :: Ord b => AGE c att b -> AGE c att b -> AGE c att b
min' = mkAGE' (NASucc (NASucc NAZero)) [||min||]

-- If we use a monomorphic type, then 'mkAGE' can deduce the number of
-- arguments.

min'' :: AGE c att Int -> AGE c att Int -> AGE c att Int
min'' = mkAGE [||min :: Int -> Int -> Int||]


-------------
-- Example --
-------------
data Root = Root { tree :: Tree }
data Tree = Node {l, r :: Tree} | Leaf {i :: Int}


smin_leaf :: AGE At_Leaf a Int
smin_leaf = val at_i 


smin_node :: HasAtt a Tree Smin Int => AGE At_Node a Int
smin_node = (smin # at_l) `min'` (smin # at_r)


smin_def = syn (Proxy :: Proxy Tree) smin $ smin_leaf `SynCons` (smin_node `SynCons` SynNil)

compilation = compileAG smin_def

------------------------------------------------------------------
-- The stuff below is boilerplate that should be generated using
-- Template Haskell.
------------------------------------------------------------------

data At_Root
type instance Prods Root = '[At_Root]

instance HasChild At_Root At_tree Tree

data At_Node; data At_Leaf
type instance Prods Tree = '[At_Node, At_Leaf]

instance HasChild At_Node At_l Tree
instance HasChild At_Node At_r Tree

instance HasChild At_Leaf At_i Int


data At_tree; at_tree :: Child At_tree Tree; at_tree = Child ('tree) (ConT ''Tree)
data At_l; at_l :: Child At_l Tree; at_l = Child ('l) (ConT ''Tree)
data At_r; at_r :: Child At_r Tree; at_r = Child ('r) (ConT ''Tree)
data At_i; at_i :: Child At_i Int; at_i = Child ('i) (ConT ''Int)

data Ival

ival :: Attr Ival Int
ival = Attr "ival" (ConT ''Int)

data Smin

smin :: Attr Smin Int
smin = Attr "smin" (ConT ''Int)

data Sres

sres :: Attr Sres Tree
sres = Attr "sres" (ConT ''Tree)
