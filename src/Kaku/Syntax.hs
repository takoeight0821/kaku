{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}

module Kaku.Syntax where

import Kaku.Outputable
  ( Outputable (ppr),
    maybeParens,
    viaOutputable,
  )
import Prettyprinter (Pretty (pretty), align, hsep, (<+>))

newtype Name
  = -- | A name for a variable, function, or type.
    Name Text
  deriving (Eq, Ord, Show)

instance Pretty Name where
  pretty (Name name) = pretty name

instance Outputable Name where
  ppr _ (Name name) = pretty name

data Expr a where
  -- | Variable
  Var :: Name -> Expr a
  -- | Lambda abstraction
  Lambda :: Name -> Expr a -> Expr a
  -- | Application
  App :: Expr a -> [Expr a] -> Expr a

deriving instance Eq (Expr a)

deriving instance Ord (Expr a)

deriving instance Show (Expr a)

instance Pretty (Expr a) where
  pretty = viaOutputable

instance Outputable (Expr a) where
  ppr _ (Var name) = ppr 0 name
  ppr l (Lambda name body) =
    maybeParens (l > 10) $
      "\\" <+> ppr 0 name <+> "->" <+> ppr 0 body
  ppr l (App fun args) =
    maybeParens (l > 10) $
      align $
        ppr 0 fun <+> hsep (map (ppr 10) args)