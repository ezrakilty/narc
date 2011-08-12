-- | A direct representation of SQL queries.

module Database.Narc.SQL where

import Data.List (nub, intercalate)

import Database.Narc.Common
import Database.Narc.Type
import Database.Narc.Util (u, mapstrcat)

import Numeric.Unary

-- | The representation of SQL queries (e.g. @select R from Ts where B@)

-- (This is unpleasant; it should probably be organized into various
-- syntactic classes.)
data Query =
    Select {
      rslt :: Row,
      tabs :: [(Tabname, Tabname, Type)],
      cond :: [QBase]
    }
    | Union Query Query
      deriving(Eq, Show)

type Row = [(Field, QBase)]

-- | Atomic-typed query fragments.
data QBase =
      Lit DataItem
    | Not QBase
    | Op QBase Op QBase
    | Field String String
    | If QBase QBase QBase
    | Exists Query
      deriving (Eq, Show)

data DataItem = Num Integer
              | Bool Bool
              | String String
  deriving (Eq, Show)

-- | Binary operators used in queries.
data Op = Eq | NonEq | Less | LessOrEq | Greater | GreaterOrEq
        | Plus | Minus | Times | Divide
        deriving(Eq, Show)

-- | Unary operators used in queries.
data UnOp = Min | Max | Count | Sum | Average
        deriving (Eq, Show)

-- | The trivial query, returning no rows.
emptyQuery = Select {rslt = [], tabs = [], cond = [Lit (Bool False)]}

-- | @sizeQuery@ returns the number of nodes in a query. It's
-- | abstracted to Num to allow using Unary, and then ``lazily''
-- | counting up to a certain amount. This helps if you only want to
-- | know whether a (potentially-enormous) query is larger than some
-- | modest cutoff.
sizeQuery :: Num a => Query -> a
sizeQuery  (q@(Select _ _ _)) =
    1 + (sum (map sizeQueryB (cond q)) +
       sum (map sizeQueryB (map snd (rslt q))))
sizeQuery (Union a b) = 1 + (sizeQuery a + sizeQuery b)

sizeQueryB :: Num a => QBase -> a
sizeQueryB (Lit _)     = 1
sizeQueryB (Not q)     = 1 + (sizeQueryB q)
sizeQueryB (Op a op b) = 1 + (sizeQueryB a + sizeQueryB b)
sizeQueryB (If c a b)  = 1 + (sizeQueryB c + sizeQueryB a + sizeQueryB b)
sizeQueryB (Field t f) = 1
sizeQueryB (Exists q)  = 1 + (sizeQuery q)

-- Basic functions on query expressions --------------------------------

freevarsQuery (q@(Select _ _ _)) = 
    (concatMap (freevarsQueryB . snd)  (rslt q))
    `u`
    (nub $ concat $ map freevarsQueryB (cond q))
freevarsQuery _ = []

freevarsQueryB (Op lhs op rhs) =
    nub (freevarsQueryB lhs ++ freevarsQueryB rhs)
freevarsQueryB (Not arg) = freevarsQueryB arg
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
serialize (Union l r) =
    "(" ++ serialize l ++ ") union (" ++ serialize r ++ ")"

serializeRow (flds) =
    mapstrcat ", " (\(x, expr) -> serializeAtom expr ++ " as " ++ x) flds

serializeAtom (Lit lit) = serializeLit lit
serializeAtom (Not expr) = "not(" ++ serializeAtom expr ++ ")"
serializeAtom (Op l op r) = 
    serializeAtom l ++ " " ++ serializeOp op ++ " " ++ serializeAtom r
serializeAtom (Field rec fld) = rec ++ "." ++ fld
serializeAtom (If cond l r) = 
    "case when " ++ serializeAtom cond ++
    " then " ++ serializeAtom l ++
    " else " ++ serializeAtom r ++
    " end)"
serializeAtom (Exists q) =
    "exists (" ++ serialize q ++ ")"

serializeLit (Num i) = show i
serializeLit (Bool b) = show b
serializeLit (String s) = show s

serializeOp Eq = "="
serializeOp NonEq = "<>"
serializeOp Less = "<"
serializeOp Greater = ">"
serializeOp LessOrEq = "<="
serializeOp GreaterOrEq = ">="
serializeOp Plus = "+"
serializeOp Minus = "-"
serializeOp Times = "*"
serializeOp Divide = "/"
