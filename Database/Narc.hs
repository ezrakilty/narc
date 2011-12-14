{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | Query SQL databases using Nested Relational Calculus embedded in
-- Haskell.
-- 
-- Many of the functions in this module are in fact the syntactic 
-- forms of the embedded language. Use them as, for example:
-- 
-- As an example, suppose we have a flat, normalized schema for a set
-- of teams and their players:
-- 
-- > teamsTable   = table "teams"   [("name", TString), ("id",     TNum)]
-- > playersTable = table "players" [("name", TString), ("teamId", TNum)]
--
-- We can denormalize it into a *nested* table of teams with their
-- full player rosters as follows:
-- 
-- > teamRosters = foreach teamsTable $ \t ->
-- >               singleton (record [("teamName", project t "name"),
-- >                                  ("roster", foreach playersTable $ \p ->
-- >                                             having (primApp "=" [p ./ "teamId", t ./ "id"]) $
-- >                                               (singleton (record [("name", (project p "name"))])))])
-- 
-- And we can return a list of those teams with at least 9 players as follows:
--
-- > validTeams = foreach teamRosters $ \t ->
-- >              having (primApp ">=" [(primApp "length" [t ./ "roster"]), cnst (9::Integer)]) $
-- >              singleton (record [("teamName", project t "teamName")])
--
-- The intermediate data structure, @teamRosters@, used nested lists,
-- and although that isn't a SQL datatype, our full query is compiled
-- into the following SQL by Narc:
--
-- > select _0.name as teamName
-- > from teams as _0, (select count(*) as count
-- >                    from players as _1
-- >                    where _1.teamId = _0.id as x where x.count >= 9)

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
import Database.Narc.Fallible
import Database.Narc.Pretty
import Database.Narc.AST.Pretty
import Database.Narc.SQL.Pretty
import qualified Database.Narc.SQL as SQL
import Database.Narc.Type as Type
import Database.Narc.TypeInfer
import Database.Narc.Util
import Database.Narc.Embed

import Database.Narc.HDBC

-- Example query

example_dull :: Term ()
example_dull = (Comp "x" (Table "foo" [("a", TBool)], ())
                (If (Project (Var "x", ()) "a", ())
                 (Singleton (Var "x", ()), ())
                 (Nil, ()), ()), ())

-- | Infer types for a Narc term and convert it to an equivalent SQL query.
typeCheckAndCompile :: Term a -> SQL.Query
typeCheckAndCompile = compile [] . runTyCheck []

-- | Translate a Narc term to an SQL query string--perhaps the central
-- | function of the interface.
narcToSQLString :: NarcTerm -> String
narcToSQLString = SQL.serialize . narcToSQL

-- | Translate a Narc term to an SQL query.
narcToSQL :: NarcTerm -> SQL.Query
narcToSQL = typeCheckAndCompile . realize
