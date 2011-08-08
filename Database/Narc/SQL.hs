-- | A direct representation of SQL queries.

module Database.Narc.SQL where

import Data.List (nub, intercalate)

import Database.Narc.Common
import Database.Narc.Type
import Database.Narc.Util (u, mapstrcat)

-- | The representation of SQL queries (e.g. @select R from Ts where B@)

-- (This is unpleasant; it should probably be organized into various
-- syntactic classes.)
data Query =
    Select {
      rslt :: Query,                      -- TBD: make this a list
      tabs :: [(Tabname, Tabname, Type)],
      cond :: [QBase]
    }
    | QRecord [(Field, QBase)]
    | QUnion Query Query
      deriving(Eq, Show)

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
emptyQuery = Select {rslt = QRecord [], tabs = [], cond = [BBool False]}

-- | The exact number of nodes in a SQL query.
sizeQueryExact :: Query -> Integer
sizeQueryExact (q@(Select _ _ _)) =
    sizeQueryExact (rslt q) + (sum $ map sizeQueryExactB (cond q))
sizeQueryExact (QRecord fields) = sum [sizeQueryExactB b | (a, b) <- fields]
sizeQueryExact (QUnion m n) = sizeQueryExact m + sizeQueryExact n

sizeQueryExactB (BNum n) = 1
sizeQueryExactB (BBool b) = 1
sizeQueryExactB (BNot q) = 1 + sizeQueryExactB q
sizeQueryExactB (BOp a op b) = 1 + sizeQueryExactB a + sizeQueryExactB b
sizeQueryExactB (BField t f) = 1
sizeQueryExactB (BExists q) = 1 + sizeQueryExact q

data Unary = Z | S Unary
    deriving (Eq, Show)

instance Num Unary where
    Z     + y = y
    x     + Z = x
    (S x) + y = S (x `rightPlus` y)

    abs x = x
    signum Z = Z
    signum (S x) = S Z
    fromInteger x | 0 == x = Z
                  | 0 <= x = S (fromInteger (x-1))
                  | otherwise = error "unary represents positive integers only"

    -- | Multiplication. Discouraged because slow.
    Z * y = Z
    x * Z = Z
    (S x) * y = y + (x * y)

instance Ord Unary where
    min Z y = Z
    min x Z = Z
    min (S x) (S y) = S (min x y)

-- | right-recursive version of (+), to balance the recursion.
rightPlus :: Unary -> Unary -> Unary
rightPlus Z     y = y
rightPlus x     Z = x
rightPlus x (S y) = S (x + y)

uToIntMax :: Unary -> Integer -> Integer
uToIntMax x max = loop x max 0
    where loop Z max result = result
          loop (S z) max result | result < max  = loop z max (result+1)
                                | result >= max = result

-- | @sizeQuery@ approximates the size of a query by calling giving up
-- | its node count past a certain limit (currently limit = 100, below).
sizeQuery :: Query -> Unary
sizeQuery q = loop q
  where loop :: Query -> Unary
        loop (q@(Select _ _ _)) =
            S (sum (map sizeQueryB (cond q)) + loop (rslt q))
        loop (QRecord fields) = sum (map sizeQueryB (map snd fields))
        loop (QUnion a b) = S (loop a + loop b)

sizeQueryB :: QBase -> Unary
sizeQueryB (BNum i) = 1
sizeQueryB (BBool b) = 1
sizeQueryB (BNot q) = S (sizeQueryB q)
sizeQueryB (BOp a op b) = S (sizeQueryB a + sizeQueryB b)
sizeQueryB (BField t f) = 1
sizeQueryB (BExists q) = S (sizeQuery q)

-- Basic functions on query expressions --------------------------------

freevarsQuery (q@(Select _ _ _)) = 
    (freevarsQuery (rslt q))
    `u`
    (nub $ concat $ map freevarsQueryB (cond q))
freevarsQuery (QRecord fields) = concatMap (freevarsQueryB . snd) fields
freevarsQuery _ = []

freevarsQueryB (BOp lhs op rhs) = nub (freevarsQueryB lhs ++ freevarsQueryB rhs)
freevarsQueryB _ = []

isQRecord (QRecord _) = True
isQRecord _ = False

-- | A ground query is one without variables or appl'ns.
-- This is a precondition of representating a real SQL query.
groundQuery :: Query -> Bool
groundQuery (qry@(Select _ _ _)) =
    all groundQueryExprB (cond qry) &&
    groundQueryExpr (rslt qry) &&
    isQRecord (rslt qry)
groundQuery (QUnion a b) = groundQuery a && groundQuery b
groundQuery (QRecord fields) = all (groundQueryB . snd) fields

groundQueryB (BExists qry) = groundQuery qry
groundQueryB (BOp b1 _ b2) = groundQueryB b1 && groundQueryB b2
groundQueryB (BNum _) = True
groundQueryB (BBool _) = True
groundQueryB (BField _ _) = True
groundQueryB (BNot a) = groundQueryB a

-- | A ground query ``expression'' is a ground query of row type.
groundQueryExpr :: Query -> Bool
groundQueryExpr (qry@(Select _ _ _)) = False
groundQueryExpr (QUnion a b) = False
groundQueryExpr (QRecord fields) = all (groundQueryExprB . snd) fields

groundQueryExprB (BExists qry) = groundQuery qry
groundQueryExprB (BOp b1 _ b2) = groundQueryExprB b1 && groundQueryExprB b2
groundQueryExprB (BNot a) = groundQueryExprB a
groundQueryExprB (BNum _) = True
groundQueryExprB (BBool _) = True
groundQueryExprB (BField _ _) = True

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

serializeRow (QRecord flds) =
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
serializeOp Plus = "<"
serializeOp Minus = "<"
serializeOp Times = "<"
serializeOp Divide = "<"
