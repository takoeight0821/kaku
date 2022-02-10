module Kaku.Outputable where

import Prettyprinter (Doc, parens)

type Level = Int

class Outputable a where
  ppr :: Level -> a -> Doc ann

viaOutputable :: Outputable a => a -> Doc ann
viaOutputable = ppr 0

maybeParens :: Bool -> Doc ann -> Doc ann
maybeParens True = parens
maybeParens False = id