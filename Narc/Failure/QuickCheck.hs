module Narc.Failure.QuickCheck where

import Test.QuickCheck

import QCUtils
import Narc.Failure

-- QuickCheck property utilities ---------------------------------------

failureToProperty :: Test.QuickCheck.Testable a => Failure a -> Property
failureToProperty (Left _) = failProp
failureToProperty (Right x) = property x

failureToPropertyIgnoreFailure :: Test.QuickCheck.Testable a => 
                                  Failure a -> Property
failureToPropertyIgnoreFailure (Left _) = ignore
failureToPropertyIgnoreFailure (Right x) = property x
