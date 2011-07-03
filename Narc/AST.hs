{-# LANGUAGE FlexibleInstances #-}

module Narc.AST (
  Term'(..),
  Term,
  Var,
  PlainTerm,
  TypedTerm,
  fvs,
  substTerm,
  strip,
  retagulate,
  rename,
  variables,
  (!),
  unit_, Const, cnst_, primApp_, var_, abs_, app_, table_, ifthenelse_,
  singleton_, nil_, union_, record_, project_, foreach_ 
) where

import Data.List as List ((\\), nub)

import Prelude hiding (abs)

import Narc.Common
import Narc.Type
import Narc.Util (alistmap, u)
import Narc.Var

-- | Terms in the nested relational calculus (represented concretely
-- | with named variables)
data Term' a = Unit | Bool Bool | Num Integer | String String
             | PrimApp String [Term a]
             | Var Var | Abs Var (Term a) | App (Term a) (Term a)
             | Table Tabname [(Field, Type)]
             | If (Term a) (Term a) (Term a)
             | Singleton (Term a) | Nil | Union (Term a) (Term a)
             | Record [(String, Term a)]
             | Project (Term a) String
             | Comp Var (Term a) (Term a)
--           | IsEmpty (Term a)
    deriving (Eq,Show)

-- | Terms whose every subexpression is annotated with a value of some
-- | particular type.
type Term a = (Term' a, a)

-- TBD: use term ::: type or similar instead of (term, type).

type PlainTerm = Term ()

type TypedTerm = Term Type

-- Operations on terms -------------------------------------------------

fvs (Unit, _) = []
fvs (Bool _, _) = []
fvs (Num _, _) = []
fvs (String _, _) = []
fvs (PrimApp prim args, _) = nub $ concat $ map fvs args
fvs (Var x, _) = [x]
fvs (Abs x n, _) = fvs n \\ [x]
fvs (App l m, _) = fvs l `u` fvs m
fvs (Table _ _, _) = []
fvs (If c a b, _) = fvs c `u` fvs a `u` fvs b
fvs (Nil, _) = []
fvs (Singleton elem, _) = fvs elem
fvs (Union m n, _) = fvs m `u` fvs n
fvs (Record fields, _) = nub $ concat $ map (fvs . snd) fields
fvs (Project targ _, _) = fvs targ
fvs (Comp x src body, _) = fvs src `u` (fvs body \\ [x])

variables = map ('y':) $ map show [0..]

rename x y (Var z, q) | x == z    = (Var y, q)
                      | otherwise = (Var z, q)
rename x y (l@(Abs z n, q)) | x == z    = l
                            | otherwise = (Abs z (rename x y n), q)
rename x y (App l m, q) = (App (rename x y l) (rename x y m), q)
rename x y (PrimApp prim args, q) = (PrimApp prim (map (rename x y) args), q)
rename x y (Singleton elem, q) = (Singleton (rename x y elem), q)
rename x y (Project targ label, q) = (Project (rename x y targ) label, q)
rename x y (Record fields, q) = (Record (alistmap (rename x y) fields), q)
rename x y (Comp z src body, q) 
    | x == z = (Comp z src body, q)
    | y == z = let y' = head $ variables \\ [y] in
               let body' = rename y y' body in
                 (Comp z (rename x y src) (rename x y body'), q)
    | otherwise= (Comp z (rename x y src) (rename x y body), q)
rename x y (String n, q) = (String n, q)
rename x y (Bool b, q) = (Bool b, q)
rename x y (Table s t, q) = (Table s t, q)
rename x y (If c a b, q) = (If (rename x y c) (rename x y a) (rename x y b), q)
rename x y (Unit, q) = (Unit, q)
rename x y (Nil, q) = (Nil, q)
rename x y (Union a b, q) = (Union (rename x y a) (rename x y b), q)

-- | substTerm x v m: substite v for x in term m
-- (Actually incorrect because it does not make substitutions in the q.)
substTerm :: Var -> Term t -> Term t -> Term t
substTerm x v (m@(Unit, _))       = m
substTerm x v (m@(Bool b, _))     = m
substTerm x v (m@(Num n, _))      = m
substTerm x v (m@(String s, _))   = m
substTerm x v (m@(Table s t, _))  = m
substTerm x v (m@(Nil, _))        = m
substTerm x v (Singleton elem, q) = (Singleton (substTerm x v elem), q)
substTerm x v (Union m n, q) = (Union (substTerm x v m) (substTerm x v n), q)
substTerm x v (m@(Var y, _)) | y == x    = v
                             | otherwise = m
substTerm x v (l @ (Abs y n, q))
    | x == y            = l
    | y `notElem` fvs v = (Abs y (substTerm x v n), q) 
    | otherwise = 
        let y' = head $ variables \\ fvs v in
        let n' = rename y y' n in
        (Abs y' (substTerm x v n'), q)
substTerm x v (App l m, q) = (App (substTerm x v l) (substTerm x v m), q)
substTerm x v (PrimApp prim args,q)= (PrimApp prim (map (substTerm x v) args),q)
substTerm x v (Project targ label, q) = (Project (substTerm x v targ) label, q)
substTerm x v (Record fields, q) = (Record (alistmap (substTerm x v) fields), q)
substTerm x v (Comp y src body, q) 
    | x == y    =
        (Comp y src' body, q)
    | y `notElem` fvs v =
        (Comp y src' (substTerm x v body), q)
    | otherwise = 
        let y' = head $ variables \\ fvs v in
        let body' = rename y y' body in
        (Comp y' src' (substTerm x v body'), q)
    where src' = (substTerm x v src)
substTerm x v (If c a b, q) = 
    (If (substTerm x v c) (substTerm x v a) (substTerm x v b), q)

-- | lazyDepth: calculate a list (poss. inf.) whose sum is the depth
-- of the term. (unused)
lazyDepth :: Term a -> [Int]
lazyDepth (Abs _ n, _) = 1 : lazyDepth n
lazyDepth (App l m, _) = 1 : zipWith max (lazyDepth l) (lazyDepth m)
lazyDepth (Project m _, _) = 1 : lazyDepth m
lazyDepth (Singleton m, _) = 1 : lazyDepth m
lazyDepth (PrimApp prim args, _) =
    1 : foldr1 (zipWith max) (map lazyDepth args)
lazyDepth (Record fields, _) =
    1 : foldr1 (zipWith max) (map (lazyDepth . snd) fields)
lazyDepth (Comp _ src body, _) =
    1 : zipWith max (lazyDepth src) (lazyDepth body)
lazyDepth _ = 1 : []

-- Generic term-recursion functions ------------------------------------

entagulate :: (Term a -> b) -> Term a -> Term b
entagulate f (Bool b, d) = (Bool b, f (Bool b, d))
entagulate f (Num n, d) = (Num n, f (Num n, d))
entagulate f (String s, d) = (String s, f (String s, d))
entagulate f (Var x, d) = (Var x, f (Var x, d))
entagulate f (Abs x n, d) = (Abs x (entagulate f n), f (Abs x n, d))
entagulate f (App l m, d) = (App (entagulate f l) (entagulate f m),
                          f (App l m, d))
entagulate f (If c a b, d) =
    (If (entagulate f c)
     (entagulate f a)
     (entagulate f b),
     f (If c a b, d))
entagulate f (Table tab fields, d) = (Table tab fields, f (Table tab fields, d))
entagulate f (Nil, d) = (Nil, f (Nil,d))
entagulate f (Singleton m, d) = (Singleton (entagulate f m),
                              f (Singleton m, d))
entagulate f (Union a b, d) =
    (Union
     (entagulate f a)
     (entagulate f b),
     f (Union a b, d))
entagulate f (Record fields, d) = (Record (alistmap (entagulate f) fields), 
                                f (Record fields, d))
entagulate f (Project m a, d) = (Project (entagulate f m) a,
                              f (Project m a, d))
entagulate f (Comp x src body, d) = 
    (Comp x (entagulate f src) (entagulate f body),
     f (Comp x src body, d))

retagulate :: (Term a -> a) -> Term a -> Term a
retagulate f (Unit, d) = (Unit, f (Unit, d))
retagulate f (Bool b, d) = (Bool b, f (Bool b, d))
retagulate f (Num n, d) = (Num n, f (Num n, d))
retagulate f (String s, d) = (String s, f (String s, d))
retagulate f (Var x, d) = (Var x, f (Var x, d))
retagulate f (Abs x n, d) = (Abs x (retagulate f n),
                             f (Abs x (retagulate f n), d))
retagulate f (App l m, d) = (App (retagulate f l) (retagulate f m),
                          f (App (retagulate f l) (retagulate f m), d))
retagulate f (PrimApp fn ar, d) = (PrimApp fn (map (retagulate f) ar),
                                   f (PrimApp fn (map (retagulate f) ar), d))
retagulate f (If c a b, d) =
    (If (retagulate f c)
     (retagulate f a)
     (retagulate f b),
     f (If (retagulate f c)
        (retagulate f a)
        (retagulate f b), d))
retagulate f (Table tab fields, d) = (Table tab fields, f (Table tab fields, d))
retagulate f (Nil, d) = (Nil, f (Nil, d))
retagulate f (Singleton m, d) = (Singleton (retagulate f m),
                              f (Singleton (retagulate f m), d))
retagulate f (Union l m, d) = (Union (retagulate f l) (retagulate f m),
                               f (Union (retagulate f l) (retagulate f m), d))
retagulate f (Record fields, d) = (Record (alistmap (retagulate f) fields), 
                                f (Record (alistmap (retagulate f) fields), d))
retagulate f (Project m a, d) = (Project (retagulate f m) a,
                              f (Project (retagulate f m) a, d))
retagulate f (Comp x src body, d) = 
    (Comp x (retagulate f src) (retagulate f body),
     f (Comp x (retagulate f src) (retagulate f body), d))

strip = entagulate (const ())

-- | numComps: Number of comprehensions in an expression, a measure of
-- the complexity of the query.
numComps (Comp x src body, _) = 1 + numComps src + numComps body
numComps (PrimApp _ args, _) = sum $ map numComps args
numComps (Abs _ n, _) = numComps n
numComps (App l m, _) = numComps l + numComps m
numComps (Singleton body, _) = numComps body
numComps (Record fields, _) = sum $ map (numComps . snd) fields
numComps (Project m _, _) = numComps m
numComps (Union a b, _) = numComps a + numComps b
numComps (Unit, _) = 0
numComps (Bool _, _) = 0
numComps (Num _, _) = 0
numComps (String _, _) = 0
numComps (Var _, _) = 0
numComps (Table _ _, _) = 0
numComps (If c a b, _) = numComps c + numComps a + numComps b
numComps (Nil, _) = 0

-- | An interface for semanticizing the Narc concrete language as
-- | desired (as per "Unembedding domain specific languages" by Atkey,
-- | Lindley and Yallop).
class NarcSem result where
    unit :: result
    bool :: Bool -> result
    num :: Integer -> result
    string :: String -> result
    primApp :: String -> [result] -> result
    var :: Var -> result
    abs :: Var -> result -> result
    app :: result -> result -> result
    table :: Tabname -> [(Field, Type)] -> result
    ifthenelse :: result -> result -> result -> result
    singleton :: result -> result
    nil :: result
    union :: result -> result -> result
    record :: [(String, result)] -> result
    project :: result -> String -> result
    foreach :: result -> Var -> result -> result
--    cnst :: Constable t => t -> result
class Constable t where cnst :: NarcSem result => t -> result
instance Constable Bool where cnst b = bool b
instance Constable Integer where cnst n = num n

-- Explicit-named builders

(!) x = (x, ())

instance NarcSem (Term'(),()) where
  unit = (!)Unit
  bool b = (!)(Bool b)
  num n = (!)(Num n)
  string n = (!)(String n)
  primApp f args = (!)(PrimApp f args)
  var x = (!)(Var x)
  abs x body = (!)(Abs x body)
  app l m = (!)(App l m)
  table tbl ty = (!)(Table tbl ty)
  ifthenelse c t f = (!)(If c t f)
  singleton x = (!)(Singleton x)
  nil = (!)Nil
  union a b = (!)(Union a b)
  record fields = (!)(Record fields)
  project body field = (!)(Project body field)
  foreach src x body = (!)(Comp x src body)
-- class Const a where cnst_ :: a -> Term ()

unit_ = (!)Unit
class Const a where cnst_ :: a -> Term ()
instance Const Bool where cnst_ b = (!)(Bool b)
instance Const Integer where cnst_ n = (!)(Num n)
primApp_ f args = (!)(PrimApp f args)
var_ x = (!)(Var x)
abs_ x body = (!)(Abs x body)
app_ l m = (!)(App l m)
table_ tbl ty = (!)(Table tbl ty)
ifthenelse_ c t f = (!)(If c t f)
singleton_ x = (!)(Singleton x)
nil_ = (!)Nil
union_ a b = (!)(Union a b)
record_ fields = (!)(Record fields)
project_ body field = (!)(Project body field)
foreach_ src x body = (!)(Comp x src body)
