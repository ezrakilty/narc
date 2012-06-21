{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances,
  UndecidableInstances {- Enable undecidable instances to allow Num => Numish implication, which should be safe (?) if we think of Num as "less than" Numish, and don't make any loops back to the lesser tier. -} #-}

-- | A litany of basic algebraas, mostly mirroring existing type
-- classes in the Haskell @Prelude@.
module Algebras where

import qualified Prelude

-- | A boolean algebra.
class BoolAlg alg where
    infixr 3 &&
    (&&) :: alg -> alg -> alg
    infixr 2 ||
    (||) :: alg -> alg -> alg
    not  :: alg -> alg

-- | The Prelude's @Bool@ is a boolean algebra.
instance BoolAlg Prelude.Bool where
    (&&) = (Prelude.&&)
    (||) = (Prelude.||)
    not  = Prelude.not

-- | An @Ord@ algebra, over a given boolean algebra as result.
class BoolAlg boolAlg =>
    Ordish alg boolAlg
  where
    infix 4 <
    (<)  :: alg -> alg -> boolAlg
    infix 4 <=
    (<=) :: alg -> alg -> boolAlg
    infix 4 >
    (>)  :: alg -> alg -> boolAlg
    infix 4 >=
    (>=) :: alg -> alg -> boolAlg
    max  :: alg -> alg -> alg
    min  :: alg -> alg -> alg

-- | An @Eq@ algebra, over a given boolean algebra as result
class BoolAlg boolAlg =>
    Eqish alg boolAlg
  where
    infix 4 ==
    (==) :: alg -> alg -> boolAlg
    infix 4 /=
    (/=) :: alg -> alg -> boolAlg
    (/=) x y = Algebras.not (x Algebras.== y)

-- | Any traditional @Eq@ also gets to be in @Eqish@ over @Bool@.
instance Prelude.Eq a =>
    Eqish a Prelude.Bool
  where
    (==) = (Prelude.==)
    (/=) = (Prelude./=)

-- | An arithmetic algebra--one mirroring @Num@.
class Numish a where
  infixl 6 +
  (+) :: a -> a -> a
  infixl 7 *
  (*) :: a -> a -> a
  infixl 6 -
  (-) :: a -> a -> a
  negate :: a -> a
  abs :: a -> a
  signum :: a -> a
  fromInteger :: Prelude.Integer -> a

-- | Anything which is a @Num@ in the Prelude is a @Numish@ algebra
-- here. The additional condition that it be an @Eq@-algebra over
-- @Bool@ may be unnecessary (TBD).
instance (Eqish a Prelude.Bool, Prelude.Num a) => Numish a where
  (+) = (Prelude.+)
  (*) = (Prelude.*)
  (-) = (Prelude.-)
  negate = Prelude.negate
  abs = Prelude.abs
  signum = Prelude.signum
  fromInteger = Prelude.fromInteger

-- | Any traditional @Ord@ also gets to be in @Ordish@ over @Bool@.
instance Prelude.Ord a =>
    Ordish a Prelude.Bool
  where
    (<) x y  = x Prelude.< y
    (<=) x y = x Prelude.<= y
    (>) x y  = x Prelude.> y
    (>=) x y = x Prelude.>= y
    min x y  = x `Prelude.min` y
    max x y  = x `Prelude.max` y
