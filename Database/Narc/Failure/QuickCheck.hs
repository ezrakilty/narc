module Database.Narc.Failure.QuickCheck where

import Test.QuickCheck hiding (Success, Failure)

import QCUtils
import Database.Narc.Fallible

-- QuickCheck property utilities ---------------------------------------

failureToProperty :: Test.QuickCheck.Testable a => Fallible a -> Property
failureToProperty (Failure _) = failProp
failureToProperty (Success x) = property x

failureToPropertyIgnoreFailure :: Test.QuickCheck.Testable a => 
                                  Fallible a -> Property
failureToPropertyIgnoreFailure (Failure _) = ignore
failureToPropertyIgnoreFailure (Success x) = property x
