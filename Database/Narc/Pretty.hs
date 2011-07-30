module Database.Narc.Pretty where

import Database.Narc.Common

-- Pretty-printing ------------------------------------------------=====

class Pretty t where
  pretty :: t -> String
