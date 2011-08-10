{-# OPTIONS_GHC -Wall -fno-warn-name-shadowing #-}

module Database.Narc.Test where

import Prelude hiding (catch)
import Control.Monad.Error ({- Error(..), throwError, -} runErrorT)

import Test.QuickCheck hiding (promote, Failure)
import Test.HUnit hiding (State, assert)

import Gensym
import QCUtils
import Numeric.Unary

import Database.Narc.AST
import Database.Narc.Compile
import Database.Narc.Failure
import qualified Database.Narc.SQL as SQL
import Database.Narc.Type as Type
import Database.Narc.TypeInfer
import Database.Narc.TermGen

normalizerTests :: Test
normalizerTests = 
    TestList [
        TestCase $ unitAssert $ 
        -- TBD: use builders here.
        let term = (Comp "x" (Table "foo" [("fop", TNum)], ())
                    (If (Bool True,())
                     (Singleton (Record
                                 [("f0", (Project (Var "x", ())
                                          "fop",()))],()),())
                     (Singleton (Record 
                                 [("f0", (Num 3, ()))], ()), ()), 
                     ()), ()) in
        let typedTerm = runErrorGensym $ infer $ term in
        (1::Integer) < (SQL.sizeQuery $ compile [] $ typedTerm)
    ]

unitTests :: Test
unitTests = TestList [tyCheckTests, normalizerTests, typingTest]

runUnitTests :: IO Counts
runUnitTests = runTestTT $ unitTests

--
-- Big QuickCheck properties
--

-- | Assertion that well-typed terms compile without throwing.
prop_compile_safe :: Property
prop_compile_safe = 
    forAll dbTableTypeGen $ \ty ->
    forAll (sized (closedTypedTermGen ty)) $ \m ->
    case tryErrorGensym (infer m) of
      Left _ -> label "ill-typed" $ property True -- ignore ill-typed terms
                                                  -- but report their occurence.
      Right (m'@(_, ty)) -> 
          classify (isDBTableTy ty) "Flat relation type" $
            let q = (compile [] $! m') in
            collect (min 100 (SQL.sizeQuery q::Unary)) $  -- NB: Counts sizes only up to ~100.
                    excAsFalse (q == q)  -- Self-comparison forces the
                                         -- value (?) thus surfacing
                                         -- any @error@s that might be
                                         -- raised.

prop_typedTermGen_tyCheck :: Property
prop_typedTermGen_tyCheck =
  forAll (sized $ typeGen []) $ \ty ->
  forAll (sized $ typedTermGen [] ty) $ \m ->
  case runGensym $ runErrorT $ infer m of
    Left _ -> False
    Right (_m', ty') -> isErrorMSuccess $ unify ty ty'

-- Main ----------------------------------------------------------------

main :: IO ()
main = do
  quickCheckWith tinyArgs prop_typedTermGen_tyCheck
  quickCheckWith tinyArgs prop_compile_safe
  _ <- runUnitTests
  return ()
