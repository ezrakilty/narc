{-# LANGUAGE TypeSynonymInstances, MultiParamTypeClasses, FlexibleInstances #-}

-- | Infix operations, and a Num instance, for more seamless embedding
-- of Narc into Haskell.
--
-- Import this module and hide the following symbols from Prelude:
--  (&&), (||), not, Num.

module Database.Narc.Embed.Ops where

import Algebras

import Database.Narc.Embed hiding ((./))

-- | NarcTerms form a boolean algebra.
instance BoolAlg NarcTerm where
    (&&) x y = primApp "and" [x,y]
    (||) x y = primApp "or" [x,y]
    not x = primApp "not" [x]

-- | NarcTerms form an @Eq@-algebra, with NarcTerms as the boolean
-- result algebra.
instance Eqish NarcTerm NarcTerm where
    (==) x y = primApp "=" [x,y]
    (/=) x y = primApp "<>" [x,y]

instance Eq NarcTerm where
    (==) x y = error "NarcTerms are not comparable with (Prelude.==). Use (Algebras.==) instead."

-- | NarcTerms form a @Num@-algebra.
-- The instance @Num NarcTerm@ is needed to support literal numbers in
-- the Haskell source.
instance Num NarcTerm where
    (+) x y = primApp "+" [x,y]
    (*) x y = primApp "*" [x,y]
    (-) x y = primApp "-" [x,y]
    negate x = primApp "-" [x] -- ??
    abs x = primApp "abs" [x] -- "Qualified name in binding position"
    signum x = primApp "/" [x, Algebras.abs x]
    fromInteger x = cnst x

-- NarcTerms form an @Ord@-algebra, with NarcTerms as the boolean
-- result algebra.
instance Ordish NarcTerm NarcTerm where
    (<)  x y = primApp "<" [x, y]
    (<=) x y = primApp "<=" [x, y]
    (>)  x y = primApp ">" [x, y]
    (>=) x y = primApp ">=" [x, y]
    max  x y = primApp "max" [x, y]
    min  x y = primApp "min" [x, y]

-- | Infix field projection: @aRecord ./ aField@ denotes the
-- projection of @aField@ from @aRecord@. Chosen to remind us of the "."
-- notation for field access in Algolish languages, and the "/"
-- notation for paths in UNIX, XQuery, etc.
infixr 9 ./
(./) = project {- Redundant with Database.Narc.Embed. Choose one? -}
