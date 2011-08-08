module Unary where

data Unary = Z | S Unary
    deriving (Eq, Show)

instance Num Unary where
    Z     + y = y
    x     + Z = x
    (S x) + y = S (x `rightPlus` y)

    abs x = x
    signum Z = Z
    signum (S x) = S Z
    fromInteger x | 0 == x = Z
                  | 0 <= x = S (fromInteger (x-1))
                  | otherwise = error "unary represents positive integers only"

    -- | Multiplication. Discouraged because slow.
    Z * y = Z
    x * Z = Z
    (S x) * y = y + (x * y)

instance Ord Unary where
    min Z y = Z
    min x Z = Z
    min (S x) (S y) = S (min x y)
    Z < Z = False
    Z < S y = True
    S x < S y = x < y

-- | right-recursive version of (+), to balance the recursion.
rightPlus :: Unary -> Unary -> Unary
rightPlus Z     y = y
rightPlus x     Z = x
rightPlus x (S y) = S (x + y)
