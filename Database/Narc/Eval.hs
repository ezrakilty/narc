module Database.Narc.Eval where

import Database.Narc.AST
import Database.Narc.Debug (debug)
import Database.Narc.Util (alistmap)

--
-- Evaluation ----------------------------------------------------------
--

-- { Values and value environments } -----------------------------------

bind x v env = (x,v):env

-- type RuntimeTerm = Term (Maybe Query)

type Env = [(Var, Value)]

data Value = VUnit | VBool Bool | VNum Integer | VString String
            | VList [Value]
            | VRecord [(String, Value)]
            | VAbs Var TypedTerm Env
        deriving (Eq, Show)

-- | Inject a data value back into a literal term that denotes it.
fromValue :: Value -> TypedTerm
fromValue VUnit = (Unit, undefined)
fromValue (VBool b) = (Bool b, undefined)
fromValue (VNum n) = (Num n, undefined)
fromValue (VString s) = (String s, undefined)
fromValue (VList xs) = foldr1 union (map singleton $ map fromValue xs)
    where union x y = (x `Union` y, undefined)
          singleton x = (Singleton x, undefined)
fromValue (VRecord fields) = (Record (alistmap fromValue fields), undefined)
fromValue (VAbs x n env) = foldr (\(y,v) -> substTerm y (fromValue v))
                           (Abs x n, undefined) env

concatVLists xs = VList $ concat [x | (VList x)<-xs]

initialEnv :: Env
initialEnv =
    []
--     [("+",
--       ((VAbs "x" (Abs "y"
--                   (PrimApp "+" [(Var "x", (TNum, openEpe), (Var "y", TNum)],
--                    Just (QOp (QVar "x") Plus (QVar "y"))), TNum) []),
--        Just (QAbs "x" (QAbs "y" (QOp (QVar "x") Plus (QVar "y"))))))]

-- | appPrim: apply a primitive function to a list of value arguments.
appPrim :: String -> [Value] -> Value
appPrim "+" [VNum a, VNum b] = VNum (a+b)
appPrim p _ = error("Unknown primitive" ++ p)

-- | eval: Evaluate a typed term in a closing environment. Captures the
-- effects performed by the term. (NB: type info is not actually used;
-- should eliminate this.)
eval :: Env -> TypedTerm -> Value
eval env (Unit, _) = (VUnit)
eval env (Bool b, q) = (VBool b)
eval env (Num n, q) = (VNum n)
eval env (String s, q) = (VString s)
eval env (PrimApp prim args, q) = 
    let (vArgs) = map (eval env) args in
    (appPrim prim vArgs)
eval env (Var x, q) =
    case lookup x env of
      Nothing -> error
                 ("Variable " ++ x ++ " not found in env " ++ show env ++ 
                  " while evaluating term.")
      Just v -> v
eval env (Abs x n, q) = (VAbs x n env')
    where env' = filter (\(a,b) -> a `elem` fvs n) env
eval env (App l m, q) = 
    let (v) = eval env l in
    let (w) = eval env m in
    case v of
      (VAbs x n env') -> 
          let env'' = bind x w env' in
          let (r) = eval env'' n in
          (r)
      _ -> error "non-function applied"
eval env (Table name fields, q) = 
    (VList [])
eval env (If c a b, _) =
    let (VBool t) = eval env c in
    let (result) = if t then eval env a else eval env b in
    (result)
eval env (Nil, _) =
    (VList [])
eval env (Singleton body, q) =
    let (v) = eval env body in
    (VList [v])
eval env (Union m n, _) =
    let (VList v) = eval env m in
    let (VList w) = eval env n in
    (VList $ v ++ w)
eval env (Record fields, q) =
    let (vFields) = [let (value) = eval env term in
                     ((name, value))
                     | (name, term) <- fields] in
    (VRecord vFields)
eval env (Project m f, q) =
    let (v) = eval env m in
    case v of
      VRecord fields -> 
          case lookup f fields of {
            Nothing -> error $ "No field " ++ f ++ " in " ++ 
                               show v ++ "(" ++ show m ++ ")" ;
            Just vField -> vField
          }
      _ -> error("Non-record value " ++ show v ++ " target of projection " ++ 
                 show(Project m f))
eval env (Comp x src body, q) =
    let (vSrc) = eval env src in
    case vSrc of
      (VList elems) -> 
          let (results) = [eval (bind x v env) body
                           | v <- elems] in
          (concatVLists results)
      _ -> error("Comprehension source was not a list.")

run = eval initialEnv
