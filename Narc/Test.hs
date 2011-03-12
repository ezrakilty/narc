{-# OPTIONS_GHC -Wall -fno-warn-name-shadowing #-}

module Narc.Test where

import Prelude hiding (catch)
import Control.Monad.State hiding (when, join)
import Control.Monad.Error ({- Error(..), throwError, -} runErrorT)

import Test.QuickCheck hiding (promote, Failure)
import Test.HUnit hiding (State, assert)

import Gensym
import QCUtils

import Narc.AST
import Narc.Compile
import Narc.Debug
import Narc.Eval
import Narc.Failure
import Narc.Pretty
import Narc.SQL
import Narc.Type as Type
import Narc.TypeInfer
import Narc.Util
import Narc.TermGen

makeNormalizerTests :: ErrorGensym Test
makeNormalizerTests = 
    do initialTyEnv <- makeInitialTyEnv 
       return$ TestList 
                 [TestCase $ unitAssert $ 
                  let term = (Comp "x" (Table "foo" [("fop", TNum)], ())
                              (If (Bool True,())
                               (Singleton (Record
                                           [("f0", (Project (Var "x", ())
                                                    "fop",()))],()),())
                               (Singleton (Record 
                                           [("f0", (Num 3, ()))], ()), ()), 
                               ()), ()) in
                  let tyTerm = runErrorGensym $ infer $ term in
                  groundQuery $ compile initialTyEnv $ tyTerm
                 ]

unitTests :: ErrorGensym Test
unitTests = do normalizerTests <- makeNormalizerTests 
               return $ TestList [tyCheckTests, normalizerTests, typingTest]

runUnitTests :: IO Counts
runUnitTests = runErrorGensym $ liftM runTestTT unitTests

--
-- Big QuickCheck properties
--

-- | Assertion that well-typed terms evaluate without throwing.
prop_eval_safe :: Property
prop_eval_safe = 
    forAll dbTableTypeGen $ \ty ->
    forAll (sized (closedTypedTermGen ty)) $ \m ->
    case tryErrorGensym (infer m) of
      Left _ -> label "ill-typed" $ property True -- ignore ill-typed terms
                                                  -- but report their occurence.
      Right (m'@(_, ty)) -> 
          isDBTableTy ty ==>
            let q = (compile [] $! m') in
            collect (sizeQuery q) $  -- NB: Counts sizes only up to ~100.
                    excAsFalse (q == q) -- Self-comparison forces the
                                        -- value (?) thus surfacing
                                        -- any @error@s that might be
                                        -- raised.

prop_typedTermGen_tyCheck :: Property
prop_typedTermGen_tyCheck =
  forAll (sized $ typeGen []) $ \ty ->
  forAll (sized $ typedTermGen (runErrorGensym makeInitialTyEnv) ty) $ \m ->
  case runGensym $ runErrorT $ infer m of
    Left _ -> False
    Right (_m', ty') -> isErrorMSuccess $ unify ty ty'

-- Main ----------------------------------------------------------------

main :: IO ()
main = quickCheckWith tinyArgs prop_eval_safe
