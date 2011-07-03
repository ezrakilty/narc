{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | Query SQL databases using Nested Relational Calculus embedded in
-- Haskell.
-- 
-- The primed functions in this module are in fact the syntactic 
-- forms of the embedded language. Use them as, for example:
-- 
-- >  foreach (table "employees" []) $ \emp ->
-- >    having (primApp "<" [cnst 20000, project emp "salary"]) $
-- >    singleton (record [(project emp "name")])

module Narc (
  -- * The type of the embedded terms
  NarcTerm,
  -- * Translation to an SQL representation
  narcTermToSQL,
  -- * The language itself
  unit, Const, primApp, abs, app, ifthenelse, singleton,
  nil, union, record, project, foreach, having
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

import Narc.AST
import Narc.Common
import Narc.Compile
import Narc.Debug
import Narc.Eval
import Narc.Failure
import Narc.Pretty
import Narc.AST.Pretty
import Narc.SQL.Pretty
import qualified Narc.SQL as SQL
import Narc.Type as Type
import Narc.TypeInfer
import Narc.Util

import Narc.HDBC

-- THE AWESOME FULL COMPILATION FUNCTION -------------------------------

typeCheckAndCompile :: Term a -> SQL.Query
typeCheckAndCompile = compile [] . runTyCheck []

-- The Narc embedded langauge-------------------------------------------

-- Example query

example_dull = (Comp "x" (Table "foo" [("a", TBool)], ())
                (If (Project (Var "x", ()) "a", ())
                 (Singleton (Var "x", ()), ())
                 (Nil, ()), ()), ())

-- HOAS-ish embedded language.

type NarcTerm = Gensym (Term ()) -- ^ Bleck. Rename.

-- | Translate a Narc term to an SQL query string--perhaps the central
-- | function of the interface.
narcTermToSQLString :: NarcTerm -> String
narcTermToSQLString = SQL.serialize . narcTermToSQL

-- | Translate a Narc term to an SQL query.
narcTermToSQL :: NarcTerm -> SQL.Query
narcTermToSQL = typeCheckAndCompile . realize

-- | Turn a HOAS representation of a Narc term into a concrete,
-- | named-binder representation.
realize :: NarcTerm -> Term ()
realize = runGensym

-- | A dummy value, or zero-width record.
unit :: NarcTerm
unit = return $ (!) Unit

-- | A polymorphic way of embedding constants into a term.
class Const' a where cnst' :: a -> NarcTerm
instance Const' Bool where cnst' b = return ((!)(Bool b))
instance Const' Integer where cnst' n = return ((!)(Num n))

-- | Apply some primitive function, such as @(+)@ or @avg@, to a list
-- of arguments.
primApp :: String -> [NarcTerm] -> NarcTerm
primApp f args =  (!) . PrimApp f <$> sequence args

-- | Create a functional abstraction.
abs :: (String -> NarcTerm) -> NarcTerm
abs fn = do
  n <- gensym
  let x = '_' : show n
  body <- fn x
  return $ (!) $ Abs x body

-- | Apply a functional term to an argument.
app :: NarcTerm -> NarcTerm -> NarcTerm
app l m = (!) <$> (App <$> l <*> m)

-- | A reference to a named database table; second argument is its
-- schema type.
table :: Tabname -> [(Field, Type)] -> NarcTerm
table tbl ty = return $ (!) $ Table tbl ty

-- | A condition between two terms, as determined by the boolean value
-- of the first term.
ifthenelse :: NarcTerm -> NarcTerm -> NarcTerm -> NarcTerm
ifthenelse c t f = (!) <$> (If <$> c <*> t <*> f)

-- | A singleton collection of one item.
singleton :: NarcTerm -> NarcTerm
singleton x = (!) . Singleton <$> x

-- | An empty collection.
nil :: NarcTerm
nil = return $ (!) $ Nil

-- | The union of two collections
union :: NarcTerm -> NarcTerm -> NarcTerm
union l r = (!) <$> (Union <$> l <*> r)

-- | Construct a record (name-value pairs) out of other terms; usually
-- used, with base values for the record elements, as the final
-- result of a query, corresponding to the @select@ clause of a SQL
-- query, but can also be used with nested results internally in a
-- query.
record :: [(String, NarcTerm)] -> NarcTerm
record fields = (!) <$> (Record <$> sequence [do expr' <- expr ; return (lbl, expr') | (lbl, expr) <- fields])

-- | Project a field out of a record value.
project :: NarcTerm -> String -> NarcTerm
project expr field = (!) <$> (Project <$> expr <*> return field)

-- | For each item in the collection resulting from the first
-- argument, give it to the function which is the second argument
-- and evaluate--this corresponds to a loop, or two one part of a
-- cross in traditional SQL queries.
foreach :: NarcTerm -> (NarcTerm -> NarcTerm) -> NarcTerm
foreach src k = do
  src' <- src
  n <- gensym
  let x = '_' : show n
  body' <- k (return (var_ x))
  return $ (!)(Comp x src' body')

-- | Filter the current iteration as per the condition in the first
-- argument. Corresponds to a @where@ clause in a SQL query.
having :: NarcTerm -> NarcTerm -> NarcTerm
having cond body = ifthenelse cond body nil

-- Example query

example' = let t = (table "foo" [("a", TBool)]) in
           foreach t $ \x -> 
           (having (project x "a")
             (singleton x))

example2' = let t = (table "foo" [("a", TNum)]) in
            let s = (table "bar" [("a", TNum)]) in
            foreach t $ \x -> 
            foreach s $ \y -> 
            ifthenelse (primApp "<" [project x "a", project y "a"])
             (singleton x)
             (singleton y)

example3' =
    let t = table "employees" [("name", TString), ("salary", TNum)] in
    foreach t $ \emp ->
    having (primApp "<" [cnst' (20000::Integer), project emp "salary"]) $
      singleton (record [("nom", project emp "name")])

-- Unit tests ----------------------------------------------------------

test_example =
    TestList [
        SQL.serialize (typeCheckAndCompile (realize example'))
        ~?= "select _0.a as a from foo as _0 where _0.a"
        ,
        SQL.serialize (typeCheckAndCompile (realize example2'))
        ~?= "(select _0.a as a from foo as _0, bar as _1 where _0.a < _1.a) union (select _1.a as a from foo as _0, bar as _1 where not(_0.a < _1.a))"
        ,
        SQL.serialize (typeCheckAndCompile (realize example3'))
        ~?= "select _0.name as nom from employees as _0 where 20000 < _0.salary"
    ]
