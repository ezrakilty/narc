{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances,
  UndecidableInstances {- Enable undecidable instances to allow Num =>
                       {- Numish implication, which should be safe (?)
                       {- if we think of Num as "less than" Numish,
                       {- and don't make any loops back to the lesser
                       {- tier. -}
#-}

module Algebras where

class BoolAlg alg where
    (&&) :: alg -> alg -> alg
    (||) :: alg -> alg -> alg
    not  :: alg -> alg

instance BoolAlg Bool where
    (&&) = (Prelude.&&)
    (||) = (Prelude.||)
    not  = Prelude.not

class BoolAlg boolAlg =>
    Ordish alg boolAlg
  where
    (<)  :: alg -> alg -> boolAlg
    (<=) :: alg -> alg -> boolAlg
    (>)  :: alg -> alg -> boolAlg
    (>=) :: alg -> alg -> boolAlg
    max  :: alg -> alg -> alg
    min  :: alg -> alg -> alg

class BoolAlg boolAlg =>
    Eqish a boolAlg
  where
    (==) :: a -> a -> boolAlg
    (/=) :: a -> a -> boolAlg
    (/=) x y = Algebras.not (x Algebras.== y)

-- | Any traditional @Eq@ also gets to be in @Eqish@ against @Bool@.
instance Eq a =>
    Eqish a Bool
  where
    (==) = (Prelude.==)
    (/=) = (Prelude./=)

class Numish a where
  (+) :: a -> a -> a
  (*) :: a -> a -> a
  (-) :: a -> a -> a
  negate :: a -> a
  abs :: a -> a
  signum :: a -> a
  fromInteger :: Integer -> a

instance (Eqish a Bool, Num a) => Numish a where
  (+) = (Prelude.+)
  (*) = (Prelude.*)
  (-) = (Prelude.-)
  negate = Prelude.negate
  abs = Prelude.abs
  signum = Prelude.signum
  fromInteger = Prelude.fromInteger

-- | Any traditional @Ord@ also gets to be in @Ordish@ against @Bool@.
instance Ord a =>
    Ordish a Bool
  where
    (<) x y  = x Prelude.< y
    (<=) x y = x Prelude.<= y
    (>) x y  = x Prelude.> y
    (>=) x y = x Prelude.>= y
    min x y  = x `Prelude.min` y
    max x y  = x `Prelude.max` y
