module Narc.Pretty where

import Narc.Common

-- Pretty-printing ------------------------------------------------=====

class Pretty t where
  pretty :: t -> String
