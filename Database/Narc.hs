{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | Query SQL databases using Nested Relational Calculus embedded in
-- Haskell.
-- 
-- The primed functions in this module are in fact the syntactic 
-- forms of the embedded language. Use them as, for example:
-- 
-- > let employeesSchema = [("name", TString), ("salary", TNum)] in
-- > let employeesTable = table "employees" employeesSchema in
-- > foreach employeesTable $ \emp -> 
-- >   having (primApp "<" [cnst 20000, project emp "salary"]) $
-- >   singleton (record [("name", project emp "name")])

module Database.Narc (
  -- * Translation to an SQL representation
  narcToSQL, narcToSQLString,
  SQL.serialize,
  -- * The language itself
  unit, table, cnst, primApp, abs, app, ifthenelse, singleton,
  nil, union, record, project, foreach, having, result,
  Type(..),
) where

import Prelude hiding (abs, catch)
import Control.Exception (catch, throwIO, evaluate, SomeException)
import Control.Monad.State hiding (when, join)
import Control.Monad.Error (throwError, runErrorT, Error(..))
import Data.List (nub, (\\), sort, sortBy, groupBy, intersperse)
import Data.Maybe (fromJust, isJust, fromMaybe)

import Control.Applicative ((<$>), (<*>))
import Foreign (unsafePerformIO)            -- FIXME

import Test.QuickCheck hiding (promote, Failure)
import QCUtils
import Test.HUnit hiding (State, assert)

import Debug.Trace

import Gensym

import Database.Narc.AST
import Database.Narc.Common
import Database.Narc.Compile
import Database.Narc.Debug
import Database.Narc.Eval
import Database.Narc.Failure
import Database.Narc.Pretty
import Database.Narc.AST.Pretty
import Database.Narc.SQL.Pretty
import qualified Database.Narc.SQL as SQL
import Database.Narc.Type as Type
import Database.Narc.TypeInfer
import Database.Narc.Util
import Database.Narc.Embed

import Database.Narc.HDBC

-- THE AWESOME FULL COMPILATION FUNCTION -------------------------------

typeCheckAndCompile :: Term a -> SQL.Query
typeCheckAndCompile = compile [] . runTyCheck []

-- The Narc embedded langauge-------------------------------------------

-- Example query

example_dull = (Comp "x" (Table "foo" [("a", TBool)], ())
                (If (Project (Var "x", ()) "a", ())
                 (Singleton (Var "x", ()), ())
                 (Nil, ()), ()), ())

-- | Translate a Narc term to an SQL query string--perhaps the central
-- | function of the interface.
narcToSQLString :: NarcTerm -> String
narcToSQLString = SQL.serialize . narcToSQL

-- | Translate a Narc term to an SQL query.
narcToSQL :: NarcTerm -> SQL.Query
narcToSQL = typeCheckAndCompile . realize
