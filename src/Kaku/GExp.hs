{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Kaku.GExp where

import Data.Functor.Classes (Eq1 (liftEq))
import Kaku.Outputable (Outputable (ppr), St, fresh, viaOutputable)
import Prettyprinter
  ( Doc,
    Pretty (pretty),
    align,
    indent,
    parens,
    vsep,
    (<+>),
  )
import qualified Text.Show (show)

-- Based on https://github.com/nachivpn/nbe-edsl

-- * Expressions

-- | Primitive operations
data GPrim c a where
  Mul :: GExp c Int -> GExp c Int -> GPrim c Int
  Add :: GExp c Int -> GExp c Int -> GPrim c Int
  Rec :: c a => GExp c Int -> GExp c (Int -> a -> a) -> GExp c a -> GPrim c a

instance Outputable (GPrim c a) where
  ppr (Mul t u) = do
    t' <- ppr t
    u' <- ppr u
    pure $ parens $ t' <+> "*" <+> u'
  ppr (Add t u) = do
    t' <- ppr t
    u' <- ppr u
    pure $ parens $ t' <+> "+" <+> u'
  ppr (Rec n f t) = do
    n' <- ppr n
    f' <- ppr f
    t' <- ppr t
    pure $ parens $ "rec" <+> n' <+> f' <+> t'

-- | Higher-order abstract syntax for expressions
data GExp c a where
  -- | Variables
  Var :: c a => Text -> GExp c a
  -- | Constants and primitives
  Lift :: PrimTy a => a -> GExp c a
  Prim :: GPrim c a -> GExp c a
  -- | Functions
  Lam :: (c a, c b) => (GExp c a -> GExp c b) -> GExp c (a -> b)
  App :: c a => GExp c (a -> b) -> GExp c a -> GExp c b
  -- | Products
  Unit :: GExp c ()
  Pair :: (c a, c b) => GExp c a -> GExp c b -> GExp c (a, b)
  Fst :: c b => GExp c (a, b) -> GExp c a
  Snd :: c a => GExp c (a, b) -> GExp c b
  -- | Sums
  Inl :: c a => GExp c a -> GExp c (Either a b)
  Inr :: c b => GExp c b -> GExp c (Either a b)
  Case :: (c a, c b, c d) => GExp c (Either a b) -> GExp c (a -> d) -> GExp c (b -> d) -> GExp c d

instance Outputable (GExp c a) where
  ppr (Var x) = pure $ pretty x
  ppr (Lift x) = pure $ pprPrimTy x
  ppr (Prim x) = ppr x
  ppr (Lam f) = do
    x <- fresh "x"
    fx' <- ppr (f (Var x))
    pure $ parens $ "\\" <> pretty x <> "." <+> fx'
  ppr (App f u) = do
    f' <- ppr f
    u' <- ppr u
    pure $ f' <+> u'
  ppr Unit = pure "()"
  ppr (Pair t u) = do
    t' <- ppr t
    u' <- ppr u
    pure $ parens $ t' <> "," <+> u'
  ppr (Fst t) = do
    t' <- ppr t
    pure $ "fst" <+> t'
  ppr (Snd t) = do
    t' <- ppr t
    pure $ "snd" <+> t'
  ppr (Inl t) = do
    t' <- ppr t
    pure $ "inl" <+> t'
  ppr (Inr t) = do
    t' <- ppr t
    pure $ "inr" <+> t'
  ppr (Case s f g) = do
    s' <- ppr s
    f' <- ppr f
    g' <- ppr g
    pure $
      align $
        vsep
          [ "Case" <+> s' <+> "of",
            indent 2 $ "inl ->" <+> f',
            indent 2 $ "inr ->" <+> g'
          ]

instance Pretty (GExp c a) where
  pretty = viaOutputable

instance Show (GExp c a) where
  show = show . pretty

-- * Equality checking

freshCmp :: St Text
freshCmp = fresh "_"

eqGPrim :: GPrim c a -> GPrim c b -> St Bool
eqGPrim (Mul t u) (Mul t' u') =
  andM [eqGExpSt t t', eqGExpSt u u']
eqGPrim (Add t u) (Add t' u') =
  andM [eqGExpSt t t', eqGExpSt u u']
eqGPrim (Rec n f t) (Rec n' f' t') =
  andM [eqGExpSt n n', eqGExpSt f f', eqGExpSt t t']
eqGPrim _ _ = pure False

eqGExpSt :: GExp c a -> GExp c b -> St Bool
eqGExpSt (Var s) (Var s') = pure $ s == s'
eqGExpSt (Lift a) (Lift a') = pure $ go pTypeRep pTypeRep a a'
  where
    go :: PTypeRep a -> PTypeRep b -> a -> b -> Bool
    go PTInt PTInt x x' = x == x'
    go PTText PTText x x' = x == x'
    go _ _ _ _ = False
eqGExpSt (Prim x) (Prim x') = eqGPrim x x'
eqGExpSt (Lam f) (Lam f') = do
  x <- freshCmp
  eqGExpSt (f (Var x)) (f' (Var x))
eqGExpSt (App f u) (App f' u') =
  andM [eqGExpSt f f', eqGExpSt u u']
eqGExpSt Unit Unit = pure True
eqGExpSt (Pair t u) (Pair t' u') =
  andM [eqGExpSt t t', eqGExpSt u u']
eqGExpSt (Fst t) (Fst t') = eqGExpSt t t'
eqGExpSt (Snd t) (Snd t') = eqGExpSt t t'
eqGExpSt (Inl t) (Inl t') = eqGExpSt t t'
eqGExpSt (Inr t) (Inr t') = eqGExpSt t t'
eqGExpSt (Case s f g) (Case s' f' g') =
  andM [eqGExpSt s s', eqGExpSt f f', eqGExpSt g g']
eqGExpSt _ _ = pure False

eqGExp :: GExp c a -> GExp c b -> Bool
eqGExp e e' = evalState (eqGExpSt e e') 0

instance Eq1 (GExp c) where
  liftEq _ = eqGExp

-- * Type reps for induction on types

-- | Primitive types
class Eq a => PrimTy a where
  pTypeRep :: PTypeRep a

instance PrimTy Int where
  pTypeRep = PTInt

instance PrimTy Text where
  pTypeRep = PTText

pprPrimTy :: PrimTy a => a -> Doc ann
pprPrimTy = go pTypeRep
  where
    go :: PTypeRep a -> a -> Doc ann
    go PTInt x = pretty x
    go PTText x = pretty x

-- | Rep of primitive types
data PTypeRep a where
  PTInt :: PTypeRep Int
  PTText :: PTypeRep Text

-- | Rep for reifiable types
data RTypeRep c a where
  RTUnit :: c () => RTypeRep c ()
  RTInt :: c Int => RTypeRep c Int
  RTText :: c Text => RTypeRep c Text
  RTProd :: (c a, c b) => RTypeRep c a -> RTypeRep c b -> RTypeRep c (a, b)
  RTSum :: (c a, c b) => RTypeRep c a -> RTypeRep c b -> RTypeRep c (Either a b)
  RTFun :: (c a, c b) => RTypeRep c a -> RTypeRep c b -> RTypeRep c (a -> b)

-- * Utilities

comp :: (c a, c b, c d) => GExp c (b -> d) -> GExp c (a -> b) -> GExp c (a -> d)
comp g f = Lam $ App g . App f

(*.) :: (c a, c b, c d) => GExp c (b -> d) -> GExp c (a -> b) -> GExp c (a -> d)
(*.) = comp

rec :: (c a, c Int) => GExp c Int -> GExp c (Int -> a -> a) -> GExp c a -> GExp c a
rec n f m = Prim (Rec n f m)

unknown :: c a => Text -> GExp c a
unknown = Var

unit :: GExp c ()
unit = Unit

lam :: (c a, c b) => (GExp c a -> GExp c b) -> GExp c (a -> b)
lam = Lam

app :: (c a, c b) => GExp c (a -> b) -> GExp c a -> GExp c b
app = App

(*$) :: (c a, c b) => GExp c (a -> b) -> GExp c a -> GExp c b
(*$) = app

lam2 :: (c a, c b, c d, c (b -> d)) => (GExp c a -> GExp c b -> GExp c d) -> GExp c (a -> b -> d)
lam2 f = lam $ \x -> lam $ \y -> f x y

app2 :: (c a, c b, c d, c (b -> d)) => GExp c (a -> b -> d) -> GExp c a -> GExp c b -> GExp c d
app2 f x = app (app f x)

case' :: (c a, c b, c d) => GExp c (Either a b) -> GExp c (a -> d) -> GExp c (b -> d) -> GExp c d
case' = Case

instance Num (GExp c Int) where
  x + y = Prim (Add x y)
  x * y = Prim (Mul x y)
  abs = error "abs not implemented"
  signum = error "signum not implemented"
  fromInteger = Lift . fromIntegral
  negate x = Prim (Mul (Lift (-1)) x)

type BoolE = Either () ()

pattern TrueE :: Either () b
pattern TrueE = Left ()

pattern FalseE :: Either a ()
pattern FalseE = Right ()