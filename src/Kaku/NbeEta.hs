{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Kaku.NbeEta where

import Control.Monad (ap)
import Kaku.GExp

type Exp a = GExp Reifiable a

type Prim a = GPrim Reifiable a

-- | neutrals
data Ne a where
  NVar :: Reifiable a => Text -> Ne a
  NApp :: Reifiable a => Ne (a -> b) -> Nf a -> Ne b
  NFst :: Reifiable b => Ne (a, b) -> Ne a
  NSnd :: Reifiable a => Ne (a, b) -> Ne b
  NMul :: Ne Int -> Ne Int -> Ne Int
  NRec :: Reifiable a => (Int, Ne Int) -> (Exp Int -> Exp a -> Nf a) -> Nf a -> Ne a

-- | normal forms
data Nf a where
  NUp :: Ne Text -> Nf Text
  NInt :: Int -> Nf Int
  NText :: Text -> Nf Text
  NAdd :: (Int, Ne Int) -> Nf Int -> Nf Int
  NUnit :: Nf ()
  NLam :: (Reifiable a, Reifiable b) => (Exp a -> Nf b) -> Nf (a -> b)
  NPair :: (Reifiable a, Reifiable b) => Nf a -> Nf b -> Nf (a, b)
  NInl :: (Reifiable a, Reifiable b) => Nf a -> Nf (Either a b)
  NInr :: (Reifiable a, Reifiable b) => Nf b -> Nf (Either a b)
  NCase :: (Reifiable a, Reifiable b, Reifiable c) => Ne (Either a b) -> (Exp a -> Nf c) -> (Exp b -> Nf c) -> Nf c

embNe :: Ne a -> Exp a
embNe (NVar x) = Var x
embNe (NApp f x) = App (embNe f) (embNf x)
embNe (NFst p) = Fst (embNe p)
embNe (NSnd p) = Snd (embNe p)
embNe (NMul m n) = Prim (Mul (embNe m) (embNe n))
embNe (NRec (ai, ni) f x) = Prim (Rec aini (Lam $ \x1 -> Lam $ \x2 -> embNf (f x1 x2)) (embNf x))
  where
    aini = if ai == 1 then embNe ni else Prim (Mul (Lift ai) (embNe ni))

embNf :: Nf a -> Exp a
embNf (NUp n) = embNe n
embNf (NInt x) = Lift x
embNf (NText x) = Lift x
embNf (NAdd (1, ni) (NInt 0)) = embNe ni
embNf (NAdd (ai, ni) (NInt 0)) = Prim $ Mul (Lift ai) (embNe ni)
embNf (NAdd (1, ni) p) = Prim $ Add (embNe ni) (embNf p)
embNf (NAdd (ai, ni) p) = Prim $ Add (Prim $ Mul (Lift ai) (embNe ni)) (embNf p)
embNf NUnit = Unit
embNf (NLam f) = Lam $ \x -> embNf (f x)
embNf (NPair p q) = Pair (embNf p) (embNf q)
embNf (NInl p) = Inl (embNf p)
embNf (NInr p) = Inr (embNf p)
embNf (NCase n f g) = Case (embNe n) (Lam $ embNf . f) (Lam $ embNf . g)

-- * Semantics and Reification

class Reifiable a where
  type Sem a :: Type

  -- | type rep for induction on values in semantics
  rTypeRep :: RTypeRep Reifiable a

  -- | `reify` valus in semantics to normal forms
  reify :: Sem a -> Nf a

  -- | `reflect` neutrals to semantics
  reflect :: Ne a -> Sem a

-- `quote` sematics back to expressions
quote :: Reifiable a => Sem a -> Exp a
quote = embNf . reify

instance Reifiable Text where
  type Sem Text = MDec (Either (Ne Text) Text)
  rTypeRep = RTText
  reify m = collectNf (fmap (either NUp NText) m)
  reflect n = Leaf (Left n)

instance Reifiable Int where
  type Sem Int = MDec SOPInt
  rTypeRep = RTInt
  reify = collectNf . remRedGuards . fmap reifySOPInt
  reflect n = Leaf (SAdd (1, n) (SInt 0))

instance Reifiable () where
  type Sem () = ()
  rTypeRep = RTUnit
  reify () = NUnit
  reflect _ = ()

instance (Reifiable a, Reifiable b) => Reifiable (a, b) where
  type Sem (a, b) = (Sem a, Sem b)
  rTypeRep = RTProd rTypeRep rTypeRep
  reify (x, y) = NPair (reify x) (reify y)
  reflect n = (reflect (NFst n), reflect (NSnd n))

instance (Reifiable a, Reifiable b) => Reifiable (a -> b) where
  type Sem (a -> b) = Sem a -> Sem b
  rTypeRep = RTFun rTypeRep rTypeRep
  reify f = NLam $ \e -> reify (f (eval e))
  reflect n = reflect . NApp n . reify

instance (Reifiable a, Reifiable b) => Reifiable (Either a b) where
  type Sem (Either a b) = MDec (Either (Sem a) (Sem b))
  rTypeRep = RTSum rTypeRep rTypeRep
  reify (Leaf (Left x)) = NInl (reify x)
  reify (Leaf (Right x)) = NInr (reify x)
  reify (SCase n f g) = NCase n (reify . f) (reify . g)
  reflect n = SCase n (Leaf . Left . eval) (Leaf . Right . eval)

-- * Eval

evalPrim :: forall a. Reifiable a => Prim a -> Sem a
evalPrim (Mul e1 e2) = mulSOPInt <$> eval e1 <*> eval e2
evalPrim (Add e1 e2) = addSOPInt <$> eval e1 <*> eval e2
evalPrim (Rec n f a) =
  runMDec @a $
    recSOPInt @a <$> eval n <*> pure (eval f) <*> pure (eval a)

eval :: forall a. Reifiable a => Exp a -> Sem a
eval (Var x) = reflect @a (NVar x)
eval Unit = ()
eval (Lift x) = drown x
eval (Prim p) = evalPrim p
eval (Lam f) = eval . f . quote
eval (App f e) = eval f (eval e)
eval (Pair e e') = (eval e, eval e')
eval (Fst e) = fst (eval e)
eval (Snd e) = snd (eval e)
eval (Inl e) = pure (Left (eval e))
eval (Inr e) = pure (Right (eval e))
eval (Case s f g) =
  let s' = eval s
      f' = eval f
      g' = eval g
   in runMDec @a (either f' g' <$> s')

drown :: forall a. PrimTy a => a -> Sem a
drown = go (pTypeRep @a)
  where
    go :: forall a. PTypeRep a -> a -> Sem a
    go PTInt x = Leaf (SInt x)
    go PTText x = Leaf (Right x)

-- | Normalisation
norm :: Reifiable a => Exp a -> Exp a
norm = quote . eval

-- * Semantics of sums

-- | A "Case Tree" monad to record case
-- distinctions on stuck terms of a sum type.
data MDec a where
  Leaf :: a -> MDec a
  SCase :: (Reifiable a, Reifiable b) => Ne (Either a b) -> (Exp a -> MDec c) -> (Exp b -> MDec c) -> MDec c

instance Functor MDec where
  fmap f (Leaf x) = Leaf (f x)
  fmap f (SCase n f1 f2) = SCase n (fmap f . f1) (fmap f . f2)

instance Applicative MDec where
  pure = Leaf
  (<*>) = ap

instance Monad MDec where
  return = Leaf
  Leaf x >>= f = f x
  SCase n g h >>= f = SCase n (f <=< g) (f <=< h)

-- | enables extraction of result of a case distinction (used for evaluating Case)
runMDec :: forall a. Reifiable a => MDec (Sem a) -> Sem a
runMDec = go (rTypeRep @a)
  where
    -- auxiliary function for runMDec which receives induction parameter
    go :: forall a. RTypeRep Reifiable a -> MDec (Sem a) -> Sem a
    go RTUnit _ = ()
    go RTInt m = join m
    go (RTProd a b) m = (go a (fmap fst m), go b (fmap snd m))
    go (RTFun _ b) m = \x -> go b (m <*> pure x)
    go (RTSum _ _) m = join m
    go RTText m = join m

collectNf :: Reifiable a => MDec (Nf a) -> Nf a
collectNf (Leaf x) = x
collectNf (SCase n f g) = NCase n (collectNf . f) (collectNf . g)

-- * Semantics of integers

data SOPInt where
  SInt :: Int -> SOPInt
  SAdd :: (Int, Ne Int) -> SOPInt -> SOPInt

-- | SOPInt can be reified into a integer
reifySOPInt :: SOPInt -> Nf Int
reifySOPInt (SInt a0) = NInt a0
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
  | otherwise = recSOPInt @a (SInt (x - 1)) f (f (pure (SInt x)) a)
recSOPInt (SAdd aini p) f a = reflect @a (NRec aini f' a')
  where
    f' :: Exp Int -> Exp a -> Nf a
    f' i b = reify (f (eval i) (eval b))
    a' :: Nf a
    a' = reify (recSOPInt @a p f a)

instance Eq (MDec (Nf a)) where
  m == m' = evalState (eqMDecSt m m') 0

eqMDecSt :: MDec (Nf a) -> MDec (Nf a) -> State Int Bool
eqMDecSt (Leaf x) (Leaf y) = eqGExpSt (embNf x) (embNf y)
eqMDecSt (SCase n f g) (SCase n' f' g') = do
  x <- freshCmp
  y <- freshCmp
  andM [eqGExpSt (embNe n) (embNe n'), eqMDecSt (f (Var x)) (f' (Var x)), eqMDecSt (g (Var y)) (g' (Var y))]
eqMDecSt _ _ = pure False

remRedGuards :: MDec (Nf a) -> MDec (Nf a)
remRedGuards (Leaf x) = Leaf x
remRedGuards b@(SCase _ f g)
  -- if these two functions yield same result when applied to
  -- different arguments, then they both don't use the argument
  | f (Var "_y") == g (Var "_z") = remRedGuards (f (Var "_"))
  | otherwise = b

-- * Examples

fun :: Exp (Int -> Int)
fun = Var "x"

funBeta :: Exp (Int -> Int)
funBeta = App (Lam id) fun

sum :: Exp (Either Text Text)
sum = Var "x"

sumComm :: Exp (Either Text Text -> Text)
sumComm = Lam $ \s ->
  Fst
    ( Case
        s
        (Lam $ \x -> Pair x x)
        (Lam $ \x -> Pair x x)
    )