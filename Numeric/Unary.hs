-- | Lazy natural numbers, represented using unary.
--
-- These numbers can be used when you want to start counting
-- something, but not necessarily finish; for example, you want to
-- know whether you have more than a hundred things, but you could
-- have a billion. By counting them lazily into Unary, you can
-- apply (min 100) and you'll stop when you hit this threshold.

module Numeric.Unary where

data Unary = Z | S Unary
    deriving (Eq)

instance Num Unary where
    Z     + y = y
    x     + Z = x
    (S x) + y = S (x `rightPlus` y)

    abs x = x
    signum Z = Z
    signum (S x) = S Z
    fromInteger x | 0 == x = Z
                  | 0 <= x = S (fromInteger (x-1))
                  | otherwise = unaryUnderflow

    -- | Multiplication. Discouraged because slow.
    Z * y = Z
    x * Z = Z
    (S x) * y = y + (x * y)

unaryUnderflow = error "unary represents positive integers only"

instance Ord Unary where
    min Z y = Z
    min x Z = Z
    min (S x) (S y) = S (min x y)
    x < Z = False
    Z < S y = True
    S x < S y = x < y

instance Show Unary where
    show x = show (toInteger x)

instance Enum Unary where
    succ x = S x
    pred (S x) = x
    pred Z = error "No pred of Z"
    toEnum x | 0 <= x = foldr (const S) Z [1..x]
             | x < 0 = unaryUnderflow
    fromEnum Z = 0
    fromEnum (S x) = 1 + fromEnum x

instance Real Unary where
    toRational x = error "toRational undefined"

instance Integral Unary where
    toInteger Z = 0
    toInteger (S x) = 1 + toInteger x
    quotRem x y = let (q,r) = (quotRem (toInteger x) (toInteger y)) in
                  (fromInteger q, fromInteger r)

-- | Right-recursive version of (+), to balance the recursion.
rightPlus :: Unary -> Unary -> Unary
rightPlus Z     y = y
rightPlus x     Z = x
rightPlus x (S y) = S (x + y)
