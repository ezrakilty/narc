{-# LANGUAGE TypeSynonymInstances, MultiParamTypeClasses #-}

-- | Infix operations, and a Num instance, for more seamless embedding
-- of Narc into Haskell.
--
-- Import this module and hide the following symbols from Prelude:
--  (&&), (||), not, Num.

module Database.Narc.Embed.Ops where

import Algebras

import Database.Narc.Embed

instance BoolAlg NarcTerm where
    (&&) x y = primApp "and" [x,y]
    (||) x y = primApp "or" [x,y]
    not x = primApp "not" [x]

instance Eqish NarcTerm NarcTerm where
    (==) x y = primApp "=" [x,y]
    (/=) x y = primApp "<>" [x,y]

-- instance Numish NarcTerm where
--   (+) x y = primApp "+" [x,y]
--   (*) x y = primApp "*" [x,y]
--   (-) x y = primApp "-" [x,y]
--   negate x = primApp "-" [x] -- ??
-- --  Algebras.abs x = primApp "abs" [x]
--   signum x = primApp "/" [x, Algebras.abs x]
--   fromInteger x = cnst x

instance Eq NarcTerm where
  (==) x y = error "NarcTerms are not comparable with (Prelude.==). Use (Algebras.==) instead."

-- The instance @Num NarcTerm@ is needed to support literal numbers in
-- the Haskell source.
instance Num NarcTerm where
  (+) x y = primApp "+" [x,y]
  (*) x y = primApp "*" [x,y]
  (-) x y = primApp "-" [x,y]
  negate x = primApp "-" [x] -- ??
-- Prelude.abs x = primApp "abs" [x]
  signum x = primApp "/" [x, Algebras.abs x]
  fromInteger x = cnst x

instance Ordish NarcTerm NarcTerm where
    (<)  x y = primApp "<" [x, y]
    (<=) x y = primApp "<=" [x, y]
    (>)  x y = primApp ">" [x, y]
    (>=) x y = primApp ">=" [x, y]
    max  x y = primApp "max" [x, y]
    min  x y = primApp "min" [x, y]
