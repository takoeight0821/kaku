module Kaku.Outputable where

import Prettyprinter (Doc, parens)

type St = State Int

class Outputable a where
  ppr :: a -> St (Doc ann)

fresh :: Text -> St Text
fresh x = do
  n <- get
  put (n + 1)
  pure $ x <> show n

viaOutputable :: Outputable a => a -> Doc ann
viaOutputable x = evalState (ppr x) 0

maybeParens :: Bool -> Doc ann -> Doc ann
maybeParens True = parens
maybeParens False = id