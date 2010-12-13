{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Narc where

import Prelude hiding (catch)
import Control.Exception (catch, throwIO, evaluate, SomeException)
import Control.Monad.State hiding (when, join)
import Control.Monad.Error (throwError, runErrorT, Error(..))
import List (nub, (\\), sort, sortBy, groupBy, intersperse)
import Maybe (fromJust, isJust, fromMaybe)

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

fullyCompile = compile [] . runTyCheck []

-- Builders ------------------------------------------------------------

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

-- Example query -------------------------------------------------------

example_dull = (Comp "x" (Table "foo" [("a", TBool)], ())
                (If (Project (Var "x", ()) "a", ())
                 (Singleton (Var "x", ()), ())
                 (Nil, ()), ()), ())

-- HOAS-ish builders

type HOASTerm = Gensym (Term ()) -- Bleck. Rename.

realize :: HOASTerm -> Term ()
realize = runGensym

unit' :: HOASTerm
unit' = return $ (!) Unit

primApp' :: String -> [HOASTerm] -> HOASTerm
primApp' f args =  (!) . PrimApp f <$> sequence args

abs' :: (String -> HOASTerm) -> HOASTerm
abs' fn = do
  n <- gensym
  let x = '_' : show n
  body <- fn x
  return $ (!) $ Abs x body

app' :: HOASTerm -> HOASTerm -> HOASTerm
app' l m = (!) <$> (App <$> l <*> m)

table' tbl ty = return $ (!) $ Table tbl ty

ifthenelse' :: HOASTerm -> HOASTerm -> HOASTerm -> HOASTerm
ifthenelse' c t f = (!) <$> (If <$> c <*> t <*> f)

singleton' :: HOASTerm -> HOASTerm
singleton' x = (!) . Singleton <$> x

nil' :: HOASTerm
nil' = return $ (!) $ Nil

onion' l r = (!) <$> (Union <$> l <*> r)

record' :: [(String, HOASTerm)] -> HOASTerm
record' fields = (!) <$> (Record <$> sequence [do expr' <- expr ; return (lbl, expr') | (lbl, expr) <- fields])

project' :: HOASTerm -> String -> HOASTerm
project' expr field = (!) <$> (Project <$> expr <*> return field)

foreach' :: HOASTerm -> (HOASTerm -> HOASTerm) -> HOASTerm
foreach' src k = do
  src' <- src
  n <- gensym
  let x = '_' : show n
  body' <- k (return (var x))
  return $ (!)(Comp x src' body')


-- Example query -------------------------------------------------------

example' = let t = (table' "foo" [("a", TBool)]) in
           foreach' t $ \x -> 
           (ifthenelse' (project' x "a")
            (singleton' x) 
            nil')

-- Try: fullyCompile (realize example')