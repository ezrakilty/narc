{-# LANGUAGE BangPatterns, ScopedTypeVariables #-}

module QCUtils where

import Prelude hiding (catch)
import Test.QuickCheck
import Control.Exception
import Foreign (unsafePerformIO)

import System.Random

{- Wrappers for detecting exceptions -}

-- | @propertyDefined x@ is a property asserting that @x@ can be
-- | forced without error.
propertyDefined :: a -> Property
propertyDefined exp = unsafePerformIO $ 
                      catch (do x <- evaluate exp
                                return $ property True)
                            (\(exc::SomeException) -> return $ property False)

-- | @excAsFalse x@ is a property that acts like @x@, except that it
-- | is @False@ when @x@ would throw an exception (and never throws an
-- | exception itself).
excAsFalse :: Testable a => a -> Property
excAsFalse exp = unsafePerformIO $ 
                     catch (do x <- evaluate exp
                               return $ property x)
                           (\(exc::SomeException) -> return $ property False)

-- | Convert an arbitrary value into a @Maybe@ by forcing it,
-- | catching errors and treating them as @Nothing@.
excAsNothing :: a -> Maybe a
excAsNothing exp = unsafePerformIO $ 
                     catch (do x <- evaluate exp
                               return $ Just x)
                           (\(exc::SomeException) -> return Nothing)

-- | A predicate asserting that forcing a thunk produces an error
-- | (useful for tests that want to ensure error is thrown).
throws :: a -> Bool
throws exp = unsafePerformIO $ 
             catch (do !x <- evaluate exp
                       return $ False)
                   (\(exc::SomeException) -> return True)

-- | Compare two functions at a particular input, incl. error
-- behavior.
f_equal x f g = (excAsNothing $ f x) == (excAsNothing $ g x)

{- Some simple generators -}

arbChar :: Gen Char
arbChar = elements $ ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++ ['_', ' ', '!']

arbLetter :: Gen Char
arbLetter = elements $ ['a'..'z'] ++ ['A'..'Z'] 

arbWordChar :: Gen Char
arbWordChar = frequency [(1, elements $ ['a'..'z'] ++ ['A'..'Z']),
                         (1, elements ['_'])]


arbStringLen :: Gen Char -> Int -> Gen String
arbStringLen charGen 0 = return ""
arbStringLen charGen n = do str <- arbStringLen charGen (n-1)
                            ch <- charGen
                            return $ ch : str

-- | arbString: Generate a string of some length between 0 and 6, each length 
-- with equal probability
arbString charGen = frequency [(1, arbStringLen charGen len)| len <- [0..6]]

arbStringSized charGen = sized (\n -> arbStringLen charGen n)

genIntLt n = elements [0..n-1]

vecTor :: Int -> Gen a -> Gen [a]
vecTor n _ | n < 0 = error "vector with negative # of elements"
vecTor 0 gen = return []
vecTor n gen = do x <- gen; xs <- vecTor (n-1) gen; return $ x : xs

posInt :: (Num a, Arbitrary a) => Gen a
posInt = fmap ((+1) . abs) arbitrary

nonNegInt :: (Num a, Arbitrary a) => Gen a
nonNegInt = fmap abs arbitrary

expIntGen n = frequency [(1, return n), (1, expIntGen (n+1))]

-- Combinators for writing conditional generators

whens p e = if p then e else []

{- Configurations for small, big, and huge test runs -}

small = stdArgs

big = Args {
    maxSuccess = 1000,
    maxDiscard = 1000,
    maxSize = 12,
    replay = Nothing,
    chatty = False
  }

huge = Args {
    maxSuccess = 10000,
    maxDiscard =  5000,
    maxSize = 20,
    replay = Nothing,
    chatty = False
  }

{- General list functions -}

histogram [] result = result
histogram (x : xs) result =
    histogram xs (incLookup x result)  
    where incLookup x [] = [(x, 1)]
          incLookup x ((y, yN):ys) | x == y    = (y,yN+1) : ys
                                   | otherwise = (y,yN)   : (incLookup x ys)

subsets [] = [[]]
subsets (x:xs) = 
    let xsSubsets = subsets xs in
    map (x:) xsSubsets ++ xsSubsets

chooseSubset [] n = []
chooseSubset (x:xs) 0 = []
chooseSubset (x:xs) n = if n `mod` 2 == 1 then x : chooseSubset xs (n `div` 2)
                        else chooseSubset xs (n `div` 2)

arbSubset xs = do n <- posInt :: Gen Int
                  return $ chooseSubset xs n

genEnv :: (Arbitrary a, Num a, Enum a, Arbitrary b) => a -> Gen [(a, b)]
genEnv min = 
    do n <- arbitrary
       sequence [do ty <- arbitrary; return (i, ty)
                 | i <- [min..min+pred(abs n)]]

failProp = property False

ignore = False ==> (undefined::Bool)

-- QuickCheck settings -------------------------------------------------

tinyArgs :: Args
tinyArgs = Args {
    maxSuccess = 100,
    maxDiscard = 100,
    maxSize = 8,
    replay = Nothing,
    chatty = False
  }

verySmallArgs :: Args
verySmallArgs = Args {
    maxSuccess = 1000,
    maxDiscard = 1000,
    maxSize = 12,
    replay = Nothing,
    chatty = False
  }

smallArgs :: Args
smallArgs = Args {
    maxSuccess = 10000,
    maxDiscard = 10000,
    maxSize = 16,
    replay = Nothing,
    chatty = False
  }

mediumArgs :: Args
mediumArgs = Args {
    maxSuccess = 100,
    maxDiscard = 100,
    maxSize = 100,
    replay = Nothing,
    chatty = False
  }

bigArgs :: Args
bigArgs = Args {
    maxSuccess = 1000,
    maxDiscard = 1000,
    maxSize = 500,
    replay = Nothing,
    chatty = False
  }
