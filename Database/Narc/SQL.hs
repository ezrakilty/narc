-- | A direct representation of SQL queries.

module Database.Narc.SQL where

import Data.List (nub, intercalate)

import Database.Narc.Common
import Database.Narc.Type
import Database.Narc.Util (u, mapstrcat)

import Unary

-- | The representation of SQL queries (e.g. @select R from Ts where B@)

-- (This is unpleasant; it should probably be organized into various
-- syntactic classes.)
data Query =
    Select {
      rslt :: Row,
      tabs :: [(Tabname, Tabname, Type)],
      cond :: [QBase]
    }
    | QUnion Query Query
      deriving(Eq, Show)

type Row = [(Field, QBase)]

-- | Atomic-typed query fragments.
data QBase =
      BNum Integer
    | BBool Bool
    | BNot QBase
    | BOp QBase Op QBase
    | BField String String
    | BIf QBase QBase QBase
    | BExists Query
      deriving (Eq, Show)

-- | Binary operators used in queries.
data Op = Eq | Less
        | Plus | Minus | Times | Divide
        deriving(Eq, Show)

-- | Unary operators used in queries.
data UnOp = Min | Max | Count | Sum | Average
        deriving (Eq, Show)

-- | The trivial query, returning no rows.
emptyQuery = Select {rslt = [], tabs = [], cond = [BBool False]}

-- | The exact number of nodes in a SQL query.
sizeQueryExact :: Query -> Integer
sizeQueryExact (q@(Select _ _ _)) =
    sum [sizeQueryExactB b | (a, b) <- rslt q] +
    sum (map sizeQueryExactB (cond q))
sizeQueryExact (QUnion m n) = sizeQueryExact m + sizeQueryExact n

sizeQueryExactB (BNum n) = 1
sizeQueryExactB (BBool b) = 1
sizeQueryExactB (BNot q) = 1 + sizeQueryExactB q
sizeQueryExactB (BOp a op b) = 1 + sizeQueryExactB a + sizeQueryExactB b
sizeQueryExactB (BField t f) = 1
sizeQueryExactB (BExists q) = 1 + sizeQueryExact q

-- | @sizeQuery@ approximates the size of a query by calling giving up
-- | its node count past a certain limit (currently limit = 100, below).
sizeQuery :: Query -> Unary
sizeQuery q = loop q
  where loop :: Query -> Unary
        loop (q@(Select _ _ _)) =
            S (sum (map sizeQueryB (cond q)) +
               sum (map sizeQueryB (map snd (rslt q))))
        loop (QUnion a b) = S (loop a + loop b)

sizeQueryB :: QBase -> Unary
sizeQueryB (BNum i)     = 1
sizeQueryB (BBool b)    = 1
sizeQueryB (BNot q)     = S (sizeQueryB q)
sizeQueryB (BOp a op b) = S (sizeQueryB a + sizeQueryB b)
sizeQueryB (BField t f) = 1
sizeQueryB (BExists q)  = S (sizeQuery q)

-- Basic functions on query expressions --------------------------------

freevarsQuery (q@(Select _ _ _)) = 
    (concatMap (freevarsQueryB . snd)  (rslt q))
    `u`
    (nub $ concat $ map freevarsQueryB (cond q))
freevarsQuery _ = []

freevarsQueryB (BOp lhs op rhs) =
    nub (freevarsQueryB lhs ++ freevarsQueryB rhs)
freevarsQueryB (BNot arg) = freevarsQueryB arg
freevarsQueryB _ = []

-- | Serialize a @Query@ to its ASCII SQL serialization.
-- Dies on those @Query@s that don't represent valid SQL queries.
serialize :: Query -> String
serialize q@(Select _ _ _) =
    "select " ++ serializeRow (rslt q) ++
    " from " ++ mapstrcat ", " (\(a, b, _) -> a ++ " as " ++ b) (tabs q) ++
    " where " ++ if null (cond q) then
                     "true"
                 else mapstrcat " and " serializeAtom (cond q)
serialize (QUnion l r) =
    "(" ++ serialize l ++ ") union (" ++ serialize r ++ ")"

serializeRow (flds) =
    mapstrcat ", " (\(x, expr) -> serializeAtom expr ++ " as " ++ x) flds

serializeAtom (BNum i) = show i
serializeAtom (BBool b) = show b
serializeAtom (BNot expr) = "not(" ++ serializeAtom expr ++ ")"
serializeAtom (BOp l op r) = 
    serializeAtom l ++ " " ++ serializeOp op ++ " " ++ serializeAtom r
serializeAtom (BField rec fld) = rec ++ "." ++ fld
serializeAtom (BIf cond l r) = 
    "case when " ++ serializeAtom cond ++
    " then " ++ serializeAtom l ++
    " else " ++ serializeAtom r ++
    " end)"
serializeAtom (BExists q) =
    "exists (" ++ serialize q ++ ")"

serializeOp Eq = "="
serializeOp Less = "<"
serializeOp Plus = "+"
serializeOp Minus = "-"
serializeOp Times = "*"
serializeOp Divide = "/"
