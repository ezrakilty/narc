module Narc.SQL where

import Data.List (nub)

import Narc.Common
import Narc.Type
import Narc.Util (u, union)

--
-- SQL Queries ---------------------------------------------------------
--

data Op = Eq | Less
        | Plus | Minus | Times | Divide
        deriving(Eq, Show)

data UnOp = Min | Max | Count | Sum | Average
        deriving (Eq, Show)

-- | Query: the type of SQL queries ("select R from Ts where B")
-- (This is unpleasant; it should probably be organized into various
-- syntactic classes.)
data Query = Select {rslt :: Query,                  -- make this a list
                     tabs :: [(Field, Field, Type)], -- use [(Field,Type)]
                     cond :: [Query]
                    }
           | QNum Integer
           | QBool Bool
           | QNot Query
           | QOp Query Op Query
           | QField String String
           | QRecord [(Field, Query)]
           | QUnion Query Query
           | QIf Query Query Query
           | QExists Query
        deriving(Eq, Show)

sizeQueryExact :: Query -> Integer
sizeQueryExact (q@(Select _ _ _)) =
    sizeQueryExact (rslt q) + (sum $ map sizeQueryExact (cond q))
sizeQueryExact (QNum n) = 1
sizeQueryExact (QBool b) = 1
sizeQueryExact (QNot q) = 1 + sizeQueryExact q
sizeQueryExact (QOp a op b) = 1 + sizeQueryExact a + sizeQueryExact b
sizeQueryExact (QField t f) = 1
sizeQueryExact (QRecord fields) = sum [sizeQueryExact n | (a, n) <- fields]
sizeQueryExact (QUnion m n) = sizeQueryExact m + sizeQueryExact n
sizeQueryExact (QIf c a b) = sizeQueryExact c + sizeQueryExact a + sizeQueryExact b
sizeQueryExact (QExists q) = 1 + sizeQueryExact q

sizeQuery :: Query -> Integer
sizeQuery qy = loop 0 qy
    where
      loop' :: Integer -> Query -> Integer
      loop' n qy = if n > limit then n else loop n qy

      loop :: Integer -> Query -> Integer
      loop n (q@(Select _ _ _)) = 
          let n' = foldr (\r n -> loop' n r) n (cond q) in
          loop' n' (rslt q)
      loop n (QNum i) = n + 1
      loop n (QBool b) = n + 1
      loop n (QNot q) = loop' (n+1) q
      loop n (QOp a op b) = let n' = loop' (n+1) a in loop' n' b
      loop n (QField t f) = n + 1
      loop n (QRecord fields) = foldr (\r n -> loop' n r) n (map snd fields)
      loop n (QUnion a b) = let n' = loop' (n+1) a in loop' n' b
      loop n (QIf c a b) = 
          let n' = loop' (n+1) c in
          let n'' = loop' n' a in
          loop' n'' b
      loop n (QExists q) = loop' (n+1) q

      limit = 100

-- Basic functions on query expressions --------------------------------

freevarsQuery (q@(Select _ _ _)) = 
    (freevarsQuery (rslt q))
    `u`
    (union $ map freevarsQuery (cond q))
freevarsQuery (QOp lhs op rhs) = nub (freevarsQuery lhs ++ freevarsQuery rhs)
freevarsQuery (QRecord fields) = concatMap (freevarsQuery . snd) fields
freevarsQuery _ = []

isQRecord (QRecord _) = True
isQRecord _ = False

-- | a groundQuery is a *real* SQL query--one without variables or appl'ns.
groundQuery :: Query -> Bool
groundQuery (qry@(Select _ _ _)) =
    all groundQueryExpr (cond qry) &&
    groundQueryExpr (rslt qry) &&
    isQRecord (rslt qry)
groundQuery (QUnion a b) = groundQuery a && groundQuery b
groundQuery (QExists qry) = groundQuery qry
groundQuery (QRecord fields) = all (groundQuery . snd) fields
groundQuery (QOp b1 _ b2) = groundQuery b1 && groundQuery b2
groundQuery (QNum _) = True
groundQuery (QBool _) = True
groundQuery (QField _ _) = True
groundQuery (QNot a) = groundQuery a

-- | a groundQueryExpr is an atomic-type expression.
groundQueryExpr :: Query -> Bool
groundQueryExpr (qry@(Select _ _ _)) = False
groundQueryExpr (QUnion a b) = False
groundQueryExpr (QExists qry) = groundQuery qry
groundQueryExpr (QRecord fields) = all (groundQueryExpr . snd) fields
groundQueryExpr (QOp b1 _ b2) = groundQueryExpr b1 && groundQueryExpr b2
groundQueryExpr (QNot a) = groundQueryExpr a
groundQueryExpr (QNum _) = True
groundQueryExpr (QBool _) = True
groundQueryExpr (QField _ _) = True
groundQueryExpr (QIf c a b) = all groundQueryExpr [c,a,b]
