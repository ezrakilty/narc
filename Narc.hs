{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | Query SQL databases using Nested Relational Calculus embedded in
-- Haskell.
-- 
-- The primed functions in this module are in fact the basic syntactic 
-- forms of the embedded language. Use them as, for example:
-- 
-- >  foreach' (table' "employees" []) $ \emp ->
-- >    where' (primApp' "<" [cnst' 20000, project' emp "salary"]) $
-- >    singleton' (record' [(project' emp "name")])

module Narc (-- * The type of the embedded terms
             GTerm,
             -- * Translation to an SQL representation
             fullyCompileGTerm,
             -- * The language itself
             unit', Const', primApp', abs', app', ifthenelse', singleton',
             nil', record', project', foreach'
            )
    where

import Prelude hiding (catch)
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
import Narc.SQL
import Narc.Type as Type
import Narc.TypeInfer
import Narc.Util

-- THE AWESOME FULL COMPILATION FUNCTION -------------------------------

fullyCompile :: Term a -> Query
fullyCompile = compile [] . runTyCheck []

-- Builders ------------------------------------------------------------

-- Explicit-named builders

(!) x = (x, ())

unit = (!)Unit
class Const a where cnst :: a -> Term ()
instance Const Bool where cnst b = (!)(Bool b)
instance Const Integer where cnst n = (!)(Num n)
primApp f args = (!)(PrimApp f args)
var x = (!)(Var x)
abs x body = (!)(Abs x body)
app l m = (!)(App l m)
table tbl ty = (!)(Table tbl ty)
ifthenelse c t f = (!)(If c t f)
singleton x = (!)(Singleton x)
nil = (!)Nil
onion a b = (!)(Union a b)
record fields = (!)(Record fields)
project body field = (!)(Project body field)
foreach src x body = (!)(Comp x src body)

-- Example query

example_dull = (Comp "x" (Table "foo" [("a", TBool)], ())
                (If (Project (Var "x", ()) "a", ())
                 (Singleton (Var "x", ()), ())
                 (Nil, ()), ()), ())

-- HOAS-ish builders

type GTerm = Gensym (Term ()) -- Bleck. Rename.

realize :: GTerm -> Term ()
realize = runGensym

fullyCompileGTerm :: GTerm -> Query
fullyCompileGTerm = fullyCompile . realize

-- | A dummy value, or zero-width record.
unit' :: GTerm
unit' = return $ (!) Unit

-- | A polymorphic way of embedding constants into a term.
class Const' a where cnst' :: a -> GTerm
instance Const' Bool where cnst' b = return ((!)(Bool b))
instance Const' Integer where cnst' n = return ((!)(Num n))

-- | Apply some primitive function, such as @(+)@ or @avg@, to a list
-- of arguments.
primApp' :: String -> [GTerm] -> GTerm
primApp' f args =  (!) . PrimApp f <$> sequence args

-- | Create a functional abstraction.
abs' :: (String -> GTerm) -> GTerm
abs' fn = do
  n <- gensym
  let x = '_' : show n
  body <- fn x
  return $ (!) $ Abs x body

-- | Apply a functional term to an argument.
app' :: GTerm -> GTerm -> GTerm
app' l m = (!) <$> (App <$> l <*> m)

-- | A reference to a named database table; second argument is its
-- schema type.
table' :: Tabname -> [(Field, Type)] -> GTerm
table' tbl ty = return $ (!) $ Table tbl ty

-- | A condition between two terms, as determined by the boolean value
-- of the first term.
ifthenelse' :: GTerm -> GTerm -> GTerm -> GTerm
ifthenelse' c t f = (!) <$> (If <$> c <*> t <*> f)

-- | A singleton collection of one item.
singleton' :: GTerm -> GTerm
singleton' x = (!) . Singleton <$> x

-- | An empty collection.
nil' :: GTerm
nil' = return $ (!) $ Nil

-- | The union of two collections
onion' :: GTerm -> GTerm -> GTerm
onion' l r = (!) <$> (Union <$> l <*> r)

-- | Construct a record (name-value pairs) out of other terms; usually
-- used, with base values for the record elements, as the final
-- result of a query, corresponding to the @select@ clause of a SQL
-- query, but can also be used with nested results internally in a
-- query.
record' :: [(String, GTerm)] -> GTerm
record' fields = (!) <$> (Record <$> sequence [do expr' <- expr ; return (lbl, expr') | (lbl, expr) <- fields])

-- | Project a field out of a record value.
project' :: GTerm -> String -> GTerm
project' expr field = (!) <$> (Project <$> expr <*> return field)

-- | For each item in the collection resulting from the first
-- argument, give it to the function which is the second argument
-- and evaluate--this corresponds to a loop, or two one part of a
-- cross in traditional SQL queries.
foreach' :: GTerm -> (GTerm -> GTerm) -> GTerm
foreach' src k = do
  src' <- src
  n <- gensym
  let x = '_' : show n
  body' <- k (return (var x))
  return $ (!)(Comp x src' body')

-- | Filter the current iteration as per the condition in the first
-- argument. Corresponds to a @where@ clause in a SQL query.
where' :: GTerm -> GTerm -> GTerm
where' cond body = ifthenelse' cond body nil'

-- Example query

example' = let t = (table' "foo" [("a", TBool)]) in
           foreach' t $ \x -> 
           (where' (project' x "a")
             (singleton' x))

example2' = let t = (table' "foo" [("a", TNum)]) in
            let s = (table' "bar" [("a", TNum)]) in
            foreach' t $ \x -> 
            foreach' s $ \y -> 
            ifthenelse' (primApp' "<" [project' x "a", project' y "a"])
             (singleton' x)
             (singleton' y)

example3' =
    let t = table' "employees" [("name", TString), ("salary", TNum)] in
    foreach' t $ \emp ->
    where' (primApp' "<" [cnst' (20000::Integer), project' emp "salary"]) $
      singleton' (record' [("nom", project' emp "name")])

-- Unit tests ----------------------------------------------------------

test_example =
    TestList [
        serialize (fullyCompile (realize example'))
        ~?= "select _0.a as a from foo as _0 where _0.a"
        ,
        serialize (fullyCompile (realize example2'))
        ~?= "(select _0.a as a from foo as _0, bar as _1 where _0.a < _1.a) union (select _1.a as a from foo as _0, bar as _1 where not(_0.a < _1.a))"
        ,
        serialize (fullyCompile (realize example3'))
        ~?= "(select _0.a as a from foo as _0, bar as _1 where _0.a < _1.a) union (select _1.a as a from foo as _0, bar as _1 where not(_0.a < _1.a))"
    ]
