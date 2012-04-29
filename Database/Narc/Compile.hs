{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Database.Narc.Compile (compile) where

import Data.List ((\\))

import Database.Narc.AST
import Database.Narc.AST.Pretty ()
import Database.Narc.Contract
import Database.Narc.Fallible
import Database.Narc.Pretty
import qualified Database.Narc.SQL as SQL
import Database.Narc.Type as Type
import Database.Narc.TypeInfer
import Database.Narc.Util (image, maps, alistmap)

-- -- Testing-related imports
-- import Test.QuickCheck (Property, forAll, sized)
-- import Database.Narc.TermGen
-- import Database.Narc.Eval
-- import Database.Narc.Failure

-- { Compilation } -----------------------------------------------------

etaExpandRecord :: TypedTerm -> [(String, Type)] -> TypedTerm
etaExpandRecord expr fieldTys =
    let exprTy = TRecord fieldTys in
    (Record [(field, ((Project expr field), fTy))
             | (field, fTy) <- fieldTys], 
     exprTy)

-- | Normalize DB terms in a nearly call-by-value way.
normTerm :: [(String, QType)] -- ^ An environment, typing all free vars.
         -> TypedTerm         -- ^ The term to normalize.
         -> TypedTerm
normTerm _env (m@(Unit, _ty))   = m
normTerm _env (m@(Bool _, _))   = m
normTerm _env (m@(Num _, _))    = m
normTerm _env (m@(String _, _)) = m
normTerm env (PrimApp fun args, t) = (PrimApp fun (map (normTerm env) args), t)
normTerm env (expr@(Var x, t)) = 
    -- Eta-expand at record type.
    if (maps x) env then 
        case t of
          TRecord t' -> etaExpandRecord expr t'
          _ -> (Var x, t) 
    else
      error $ "Free variable "++ x ++ " in normTerm"
normTerm _env (Abs x n, t) =
    (Abs x n, t)
normTerm env (App l m, t) = 
    let w = normTerm env m in
    case normTerm env l of 
      (Abs x n, _) -> 
          let n' = substTerm x w n in
          case tryTyCheck env $ n' of
            Success term' -> normTerm env (term')
            Failure msg   -> error ("Error " ++ msg ++
                               " substituting " ++ pretty w ++ 
                               " for " ++ x ++ " in " ++ pretty n)

      (If b l1 l2, _) ->
          (normTerm env (If b (App l1 w, t) (App l2 w, t), t))
      v@(Var _, _) -> (App v w, t)
      v -> error $ "unexpected normal form in appl posn in normTerm " ++ show v
normTerm _env (Table s t, t') = (Table s t, t')
normTerm env (If b m (Nil, _), t@(TList _)) =
    let b' = normTerm env b in
    case normTerm env m of
      (Nil, _)           -> (Nil, t)
      (Singleton m', _)  -> (If b' (Singleton m', t) (Nil, t), t)
      (Table s fTys, _)  -> (If b' (Table s fTys, t) (Nil, t), t)
      (Comp x l m', _)   -> normTerm env (Comp x l (If b' m' (Nil, t), t), t)
      (m1 `Union` m2, _) -> ((normTerm env (If b' m1 (Nil, t), t)) `Union`
                             (normTerm env (If b' m2 (Nil, t), t)), t)
      v@(If _ _ _, _)    -> (If b' v (Nil, t), t)
      v -> error $ "Unexpected normal form in conditional body in normTerm: " ++
                    show v
normTerm env (If b@(_,bTy) m n, t@(TList _)) = -- The case where n /= Nil
    ((normTerm env (If b m (Nil, t), t)) `Union` 
     (normTerm env (If (PrimApp "not" [b], bTy) n (Nil, t), t)), t)
normTerm env (If b m n, t@(TRecord fTys)) =
    let b' = normTerm env b in
    let (Record mFields, _) = normTerm env m
        (Record nFields, _) = normTerm env n in
    (Record [(l, (If b' (image l mFields) (image l nFields), (image l fTys)))
             | (l, _) <- mFields],
     t)
normTerm env (If b m n, t) = 
    (If (normTerm env b) (normTerm env m) (normTerm env n), t)
normTerm env (Singleton m, t) = (Singleton (normTerm env m), t)
normTerm _env (Nil, t) = (Nil, t)
normTerm env (m `Union` n, t) = ((normTerm env m) `Union` (normTerm env n), t)
normTerm env (Record fields, t) =
    (Record [(a, normTerm env m) | (a, m) <- fields], t)
normTerm env (Project argTerm label, t) = 
    case normTerm env argTerm of
      (Record fields, _) -> case (lookup label fields) of 
                              Just x -> x 
                              Nothing -> error $ "no field " ++ label
      -- Ah, the following not necessary because If pushes into records.
      (If condn v1 v2,_) ->
          normTerm env (If condn
                        (Project v1 label, t)
                        (Project v2 label, t), t)
      v@(Var _x, _) -> (Project v label, t)
      v -> error $ "Unexpected normal form in body of Project in normTerm: " ++ 
                    show v
normTerm env (Comp x src body, t) =
    case normTerm env src of
      (Nil, _) -> (Nil, t)
      (Singleton src', _) -> 
          let body' = substTerm x src' body in
          case tryTyCheck env body' of
            Success body'' -> normTerm env body''
            Failure msg -> error ("Error " ++ msg ++
                                  "\nWhile substituting " ++ pretty src' ++ 
                                  "\nfor " ++ x ++ "\nin " ++ pretty body)
      (Comp y src2 body2, _) ->
          -- Freshen @y@ over @src@ with respect to @body@ (that of
          -- the outer comprehension), because we're widening the
          -- scope of @y@ to include @body@.
          let (y', body') = if y `elem` fvs body then
                              let newY = minFreeFor body in
                              (newY, rename y newY body)
                         else (y, body)
          in
            (normTerm env (Comp y' src2 (Comp x body2 body', t), t))
      (srcL `Union` srcR, _) ->
          ((normTerm env (Comp x srcL body, t)) `Union` 
           (normTerm env (Comp x srcR body, t)), t)
      (tbl @ (Table _tableName fieldTys, _)) ->
          insert (\(v',t') -> (Comp x tbl (v',t'), t')) $
                 let env' = Type.bind x ([],TRecord fieldTys) env in 
                 normTerm env' body
      (If cond' src' (Nil, _), _) ->
          assert (x `notElem` fvs cond') $
          let v = normTerm env (Comp x src' body, t) in
          insertFurther (\(v',t') -> (If cond' (v',t') (Nil, t'), t')) v
      v -> error $
             "unexpected normal form in source part of comprehension: " ++
             show v

-- Insertion functions for rebuilding a term, dropping a
-- reconstructor k down through unions and compr'ns (there must be
-- a better way!).

insert :: (TypedTerm -> TypedTerm) -> TypedTerm -> TypedTerm
insert k ((v,t) :: TypedTerm) =
    case v of
      Nil -> (Nil, t)
      n1 `Union` n2 -> ((insert k n1) `Union` (insert k n2), t)
      _ -> k (v,t)

insertFurther :: (TypedTerm -> TypedTerm) -> TypedTerm -> TypedTerm
insertFurther k ((v,t) :: TypedTerm) =
    case v of
      Nil -> (Nil, t)
      n1 `Union` n2 -> 
          ((insertFurther k n1) `Union` (insertFurther k n2), t)
      Comp x m n -> (Comp x m (insertFurther k n), t)
      _ -> k (v,t)

-- See (Bird 2010) for a better algorithm here.
minFreeFor :: Term a -> VarName
minFreeFor n = head $ variables \\ fvs n 

-- | @translateTerm@ homomorphically translates a normal-form Term to an
-- | SQL Query.
translateTerm :: TypedTerm -> SQL.Query
translateTerm (v `Union` u, _) = (translateTerm v) `SQL.Union` (translateTerm u)
translateTerm (Nil, _)         = SQL.emptyQuery
translateTerm (f@(Comp _ (Table _ _, _) _, _))                  = translateF f
translateTerm (f@(If _ _ (Nil, _), _))                          = translateF f
translateTerm (f@(Singleton (Record _, _), _))                  = translateF f
translateTerm (f@(Table _ _, _))                                = translateF f
translateTerm (v, _) = 
    error $ "translateTerm got unexpected term: " ++ pretty v

-- translateF, translateZ and translateB are named after the syntactic
-- classes (in the grammar of the normalized form) which they handle.
-- (F for "for comprehension", Z for "final bit of a nest of
-- comprehensions", and B for "base type"
translateF :: Term b -> SQL.Query
translateF (Comp x (Table tabname fTys, _) n, _) =
    let q@(SQL.Select _ _ _) = translateF n in
    SQL.Select {SQL.rslt = SQL.rslt q,
                SQL.tabs = (SQL.Table tabname, x, TRecord fTys) : SQL.tabs q,
                SQL.cond = SQL.cond q
               }
translateF (z@(If _ _ (Nil, _), _))                             = translateZ z
translateF (z@(Singleton (Record _, _), _))                     = translateZ z
translateF (z@(Table _ _, _))                                   = translateZ z
translateF (z, _) = error $ "translateF for unexpected term: " ++ pretty z

translateZ :: Term b -> SQL.Query
translateZ (If b z (Nil, _), _) =
    let q@(SQL.Select _ _ _) = translateZ z in
    let (b', extraQs) = translateB b in
    SQL.Select {SQL.rslt = SQL.rslt q,
                SQL.tabs = extraQs ++ SQL.tabs q,
                SQL.cond = b' : SQL.cond q
               }
translateZ (Singleton (Record fields, _), _) = 
    let temp = alistmap translateB fields in
    let fields' = map (\(f, (x, _)) -> (f, x)) temp in
    let extraQs = concat (map (\(_, (_, q)) -> q) temp) in
    SQL.Select {SQL.rslt = fields',
                SQL.tabs = extraQs,
                SQL.cond = []
               }
translateZ (Table tableName fTys, _) =
    SQL.Select {SQL.rslt = [(l, SQL.Field tableName l) | (l, _ty) <- fTys],
                SQL.tabs = [(SQL.Table tableName, tableName, TRecord fTys)],
                SQL.cond = []
               }
translateZ (z, _) = error $ "translateZ got unexpected term: " ++ pretty z

translateB :: Term b -> (SQL.QBase, [(SQL.Query, Tabname, Type)])
translateB (If b b' b'', _)            = 
    let ((bSql, q1), (b'Sql, q2), (b''Sql, q3)) = 
            (translateB b,
             translateB b',
             translateB b'') in
    (SQL.If bSql b'Sql b''Sql,
     q1 ++ q2 ++ q3)
translateB (Bool n, _)                 = ((SQL.Lit (SQL.Bool n)), [])
translateB (Num n, _)                  = ((SQL.Lit (SQL.Num n)), [])
translateB (String s, _)               = ((SQL.Lit (SQL.String s)), [])
translateB (Project (Var x, _) l, _)   = (SQL.Field x l, [])
translateB (PrimApp "not" [arg], _)    = let (arg', qs) = translateB arg in
                                         (SQL.Not arg', qs)
translateB (PrimApp "length" [arg], _) = (SQL.count (translateF arg))
translateB (PrimApp str [l, r], _)     = -- TBD restrict this with a guard
    let (l', lQ) = (translateB l) in
    let (r', rQ) = (translateB r) in
    (SQL.Op l' (translatePrimOp str) r', lQ ++ rQ)
translateB (b, _) = error $ "translateB got unexpected term: " ++ pretty b

translatePrimOp :: String -> SQL.Op
translatePrimOp ("<")   = SQL.Less
translatePrimOp (">")   = SQL.Greater
translatePrimOp ("<=")  = SQL.LessOrEq
translatePrimOp (">=")  = SQL.GreaterOrEq
translatePrimOp ("=")   = SQL.Eq
translatePrimOp ("<>")  = SQL.NonEq
translatePrimOp ("+")   = SQL.Plus
translatePrimOp ("-")   = SQL.Minus
translatePrimOp ("*")   = SQL.Times
translatePrimOp ("/")   = SQL.Divide
translatePrimOp ("and") = SQL.And
translatePrimOp ("or")  = SQL.Or
translatePrimOp str = error $ "unknown primitive function call: " ++ str

compile :: TyEnv -> TypedTerm -> SQL.Query
compile env = translateTerm . normTerm env

-- -- Tests

-- -- FIXME: where does this belong? It tests a function internal to this
-- -- module (normTerm) but uses testing apparatus that is defined at a
-- -- "higher" layer (Database.Narc.Test) and uses an otherwise unrelated module
-- -- (Database.Narc.Eval).
-- prop_norm_sound :: TyEnv -> Env -> Property
-- prop_norm_sound tyEnv env =
--   forAll (sized (typeGen [])) $ \t ->
--   forAll (sized (typedTermGen tyEnv t)) $ \m ->
--       isErrorMSuccess $ tryErrorGensym $ 
--       do m' <- infer m
--          return (eval env (normTerm tyEnv m') == eval env m')
