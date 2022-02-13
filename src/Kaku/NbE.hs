{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Kaku.NbE where

import Control.Monad (ap)
import Kaku.GExp (GExp (..), GPrim (..), PTypeRep (..), PrimTy (..), RTypeRep (..))
import qualified Kaku.GExp as G

type Exp a = GExp Reifiable a

type Prim a = GPrim Reifiable a

-- * Normal forms

data Ne a where
  NVar :: Reifiable a => Text -> Ne a
  NApp :: Reifiable a => Ne (a -> b) -> Nf a -> Ne b
  NFst :: Reifiable b => Ne (a, b) -> Ne a
  NSnd :: Reifiable a => Ne (a, b) -> Ne b
  NMul :: Ne Int -> Ne Int -> Ne Int
  NRec :: Reifiable a => (Int, Ne Int) -> (Exp Int -> Exp a -> Nf a) -> Nf a -> Ne a

data Nf a where
  NUp :: Ne a -> Nf a
  NLift :: PrimTy a => a -> Nf a
  NAdd :: (Int, Ne Int) -> Nf Int -> Nf Int
  NUnit :: Nf ()
  NLam :: (Reifiable a, Reifiable b) => (Exp a -> Nf b) -> Nf (a -> b)
  NPair :: (Reifiable a, Reifiable b) => Nf a -> Nf b -> Nf (a, b)
  NInl :: Reifiable a => Nf a -> Nf (Either a b)
  NInr :: Reifiable b => Nf b -> Nf (Either a b)
  NCase :: (Reifiable a, Reifiable b, Reifiable c) => Ne (Either a b) -> (Exp a -> Nf c) -> (Exp b -> Nf c) -> Nf c

-- | embed neutrals back into expressions
embNe :: Ne a -> Exp a
embNe (NVar x) = Var x
embNe (NApp f x) = App (embNe f) (embNf x)
embNe (NFst x) = Fst (embNe x)
embNe (NSnd x) = Snd (embNe x)
embNe (NMul x y) = Prim $ Mul (embNe x) (embNe y)
embNe (NRec (ai, ni) f x) = Prim (Rec aini (Lam $ \x1 -> Lam $ \x2 -> embNf (f x1 x2)) (embNf x))
  where
    aini =
      if ai == 1
        then embNe ni
        else Prim (Mul (Lift ai) (embNe ni))

-- | embed normal forms back into expressions
embNf :: Nf a -> Exp a
embNf (NUp n) = embNe n
embNf (NLift x) = Lift x
embNf (NAdd (1, ni) (NLift 0)) = embNe ni
embNf (NAdd (ai, ni) (NLift 0)) = Prim $ Mul (Lift ai) (embNe ni)
embNf (NAdd (1, ni) p) = Prim $ Add (embNe ni) (embNf p)
embNf (NAdd (ai, ni) p) = Prim $ Add (Prim $ Mul (Lift ai) (embNe ni)) (embNf p)
embNf NUnit = Unit
embNf (NLam f) = Lam (embNf . f)
embNf (NPair m n) = Pair (embNf m) (embNf n)
embNf (NInl m) = Inl (embNf m)
embNf (NInr m) = Inr (embNf m)
embNf (NCase n f g) = Case (embNe n) (Lam $ embNf . f) (Lam $ embNf . g)

-- * Semantics and Reification

class Reifiable a where
  type Sem a :: Type
  rTypeRep :: RTypeRep Reifiable a
  reify :: Sem a -> Nf a
  reflect :: Ne a -> Sem a
  runMDec :: MDec (Sem a) -> Sem a

-- | "quote" semantics back to expressions
quote :: Reifiable a => Sem a -> Exp a
quote = embNf . reify

instance Reifiable Text where
  type Sem Text = Nf Text
  rTypeRep = RTText
  reify m = m
  reflect n = NUp n
  runMDec m = collect m

instance Reifiable Int where
  type Sem Int = (MDec SOPInt, Nf Int)
  rTypeRep = RTInt
  reify = snd
  reflect n = (Leaf (SAdd (1, n) (SInt 0)), NUp n)
  runMDec m = (fst =<< m, collect (snd <$> m))

instance Reifiable () where
  type Sem () = ()
  rTypeRep = RTUnit
  reify () = NUnit
  reflect _ = ()
  runMDec _ = ()

instance (Reifiable a, Reifiable b) => Reifiable (a, b) where
  type Sem (a, b) = ((Sem a, Sem b), Nf (a, b))
  rTypeRep = RTProd rTypeRep rTypeRep
  reify = snd
  reflect n = ((reflect (NFst n), reflect (NSnd n)), NUp n)
  runMDec m = ((runMDec @a (fst . fst <$> m), runMDec @b (snd . fst <$> m)), collect (snd <$> m))

instance (Reifiable a, Reifiable b) => Reifiable (a -> b) where
  type Sem (a -> b) = (Sem a -> Sem b, Nf (a -> b))
  rTypeRep = RTFun rTypeRep rTypeRep
  reify = snd
  reflect n = (reflect . NApp n . reify, NUp n)
  runMDec m = (\x -> runMDec @b ((fst <$> m) <*> pure x), collect (snd <$> m))

instance (Reifiable a, Reifiable b) => Reifiable (Either a b) where
  type Sem (Either a b) = (MDec (Either (Sem a) (Sem b)), Nf (Either a b))
  rTypeRep = RTSum rTypeRep rTypeRep
  reify = snd
  reflect n = (SCase n (Leaf . Left . eval) (Leaf . Right . eval), NUp n)
  runMDec m = (fst =<< m, collect (snd <$> m))

-- * Evaluation

evalPrim :: forall a. Reifiable a => Prim a -> Sem a
evalPrim (Mul e1 e2) =
  let (mx, _) = eval e1
      (my, _) = eval e2
      z = mulSOPInt <$> mx <*> my
   in (z, collect $ fmap reifySOPInt z)
evalPrim (Add e1 e2) =
  let (mx, _) = eval e1
      (my, _) = eval e2
      z = addSOPInt <$> mx <*> my
   in (z, collect $ fmap reifySOPInt z)
evalPrim (Rec n f a) =
  runMDec @a $
    recSOPInt @a
      <$> fst (eval n)
      <*> pure ((.) fst . fst $ eval f)
      <*> pure (eval a)

eval :: forall a. Reifiable a => Exp a -> Sem a
eval (G.Var s) = reflect @a (NVar s)
eval G.Unit = ()
eval (G.Lift x) = drown x
eval (G.Prim p) = evalPrim p
eval (G.Lam f) = (eval . f . quote, NLam (reify . eval . f))
eval (G.App f e) = fst (eval f) (eval e)
eval (G.Pair e e') =
  let x = eval e
      y = eval e'
   in ((x, y), NPair (reify x) (reify y))
eval (G.Fst e) = fst . fst . eval $ e
eval (G.Snd e) = snd . fst . eval $ e
eval (G.Inl e) = let x = eval e in (Leaf (Left x), NInl (reify x))
eval (G.Inr e) = let x = eval e in (Leaf (Right x), NInr (reify x))
eval (G.Case e f g) =
  let (x, _) = eval e
      (f', _) = eval f
      (g', _) = eval g
   in runMDec @a (either f' g' <$> x)

drown :: forall a. PrimTy a => a -> Sem a
drown = go $ pTypeRep @a
  where
    go :: forall a. PTypeRep a -> a -> Sem a
    go PTInt x = (Leaf (SInt x), NLift x)
    go PTText x = NLift x

-- | Nomalisation
norm :: Reifiable a => Exp a -> Exp a
norm = quote . eval

-- * Semantics of integers

-- | Semantics of integers take the shape of a sum of products
-- (a_0 * x_0) + (a_1 * x_1) + ... + a_n
-- where, for each i, a_i is a constant and x_i is a neutral.
data SOPInt where
  -- | a_n
  SInt :: Int -> SOPInt
  -- | (a_i * x_i) + ...
  -- Invariant: a_i != 0
  SAdd :: (Int, Ne Int) -> SOPInt -> SOPInt

-- | SOPInt can be reified into a integer
reifySOPInt :: SOPInt -> Nf Int
reifySOPInt (SInt a0) = NLift a0
reifySOPInt (SAdd (ai, ni) p) = NAdd (ai, ni) (reifySOPInt p)

-- | addition on SOPInt
addSOPInt :: SOPInt -> SOPInt -> SOPInt
addSOPInt (SInt 0) p = p
addSOPInt (SInt a0) (SInt b0) = SInt (a0 + b0)
addSOPInt (SInt a0) (SAdd bimi p) = SAdd bimi (addSOPInt (SInt a0) p)
addSOPInt (SAdd aini ans) p = SAdd aini (addSOPInt ans p)

-- | multiplication on SOPInt
mulSOPInt :: SOPInt -> SOPInt -> SOPInt
mulSOPInt (SInt 0) _ = SInt 0
mulSOPInt (SInt 1) p = p
mulSOPInt (SInt a0) (SInt b0) = SInt (a0 * b0)
mulSOPInt (SInt a0) (SAdd (bi, mi) p)
  | a0 * bi == 0 = mulSOPInt (SInt a0) p
  | otherwise = SAdd (a0 * bi, mi) (mulSOPInt (SInt a0) p)
mulSOPInt (SAdd (ai, ni) ans) (SInt b0)
  | ai * b0 == 0 = mulSOPInt ans (SInt b0)
  | otherwise = SAdd (ai * b0, ni) (mulSOPInt ans (SInt b0))
mulSOPInt (SAdd (ai, ni) p) (SAdd (bi, mi) q)
  | ai * bi == 0 = mulSOPInt (SAdd (ai, ni) p) q
  | otherwise = SAdd (ai * bi, NMul ni mi) (mulSOPInt (SAdd (ai, ni) p) q)

-- | recursion using SOPInt
recSOPInt :: forall a. Reifiable a => SOPInt -> (Sem Int -> Sem a -> Sem a) -> Sem a -> Sem a
recSOPInt (SInt x) f a
  | x <= 0 = a
  | otherwise = recSOPInt @a (SInt (x - 1)) f (f (pure (SInt x), NLift x) a)
recSOPInt (SAdd aini p) f a = reflect @a (NRec aini f' a')
  where
    f' :: Exp Int -> Exp a -> Nf a
    f' i b = reify (f (eval i) (eval b))
    a' :: Nf a
    a' = reify (recSOPInt @a p f a)

-- * Semantics of sums

-- | A Dicision tree monad to recode case distinctions
-- on stuck terms of a sum type.
data MDec a where
  Leaf :: a -> MDec a
  SCase :: (Reifiable a, Reifiable b) => Ne (Either a b) -> (Exp a -> MDec c) -> (Exp b -> MDec c) -> MDec c

collect :: Reifiable c => MDec (Nf c) -> Nf c
collect (Leaf x) = x
collect (SCase n f g) = NCase n (collect . f) (collect . g)

instance Functor MDec where
  fmap f (Leaf x) = Leaf (f x)
  fmap f (SCase n g h) = SCase n (fmap f . g) (fmap f . h)

instance Applicative MDec where
  pure = Leaf
  (<*>) = ap

instance Monad MDec where
  (Leaf x) >>= f = f x
  (SCase n g h) >>= f = SCase n (f <=< g) (f <=< h)

-- * Examples

funNoEta :: Reifiable a => Exp (a -> a)
funNoEta = Var "x"

funBeta :: Reifiable a => Exp (a -> a)
funBeta = App (Lam id) funNoEta

sumNoEta :: Reifiable a => Exp (Either a a)
sumNoEta = Var "x"

sumComm :: Reifiable a => Exp (Either a a -> a)
sumComm = Lam $ \s ->
  Fst
    ( Case
        s
        (Lam $ \x -> Pair x x)
        (Lam $ \x -> Pair x x)
    )