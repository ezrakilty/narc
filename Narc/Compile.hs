{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Narc.Compile (compile) where

import Data.List ((\\))

import Narc.AST
import Narc.AST.Pretty ()
import Narc.Contract
import Narc.Debug (forceAndReport)
import Narc.Pretty
import Narc.Type as Type
import Narc.TypeInfer
import Narc.Util (image, maps, alistmap)
import Narc.SQL

-- { Compilation } -----------------------------------------------------

etaExpand :: TypedTerm -> [(String, Type)] -> TypedTerm
etaExpand expr fieldTys =
    let exprTy = TRecord fieldTys in
    (Record [(field, ((Project expr field), fTy))
             | (field, fTy) <- fieldTys], 
     exprTy)

-- | Normalize DB terms on a CBV evaluation strategy. First arg is an
-- environment: the variables it is ok not to normalize.
normTerm :: [(String, QType)] -> TypedTerm -> TypedTerm
normTerm _env (m@(Unit, _ty)) = m
normTerm _env (m@(Bool _b, _)) = m
normTerm _env (m@(Num _n, _)) = m
normTerm env (PrimApp fun args, t) = (PrimApp fun (map (normTerm env) args), t)
normTerm env (expr@(Var x, t)) = 
    -- Eta-expand at record type.
    if (maps x) env then 
        case t of
          TRecord t' -> etaExpand expr t'
          _ -> (Var x, t) 
    else
      error $ "Free variable "++ x ++ " in normTerm"
normTerm env (Abs x n, t) = (Abs x n, t)
normTerm env (App l m, t) = 
    let w = normTerm env m in
    case normTerm env l of 
      (Abs x n, _) -> 
          forceAndReport (
            let !n' = substTerm x w n in
            normTerm env (runTyCheck env $ n')
          ) ("susbtituting "++show w++" for "++x++" in "++show n)
      (If b l1 l2, _) ->
          (normTerm env (If b (App l1 w, t) (App l2 w, t), t))
      v@(Var x, _) -> (App v w, t)
      v -> error $ "unexpected normal form in appl posn in normTerm " ++ show v
normTerm env (Table s t, t') = (Table s t, t')
normTerm env (If b m (Nil, _), t@(TList _)) =
    let b' = normTerm env b in
    case normTerm env m of
      (Nil, _) -> (Nil, t)
      (Singleton m', _) -> (If b' (Singleton m', t) (Nil, t), t)
      (Table s fTys, _) -> (If b' (Table s fTys, t) (Nil, t), t)
      (Comp x l m', _) -> normTerm env (Comp x l (If b' m' (Nil, t), t), t)
      (m1 `Union` m2, _) -> ((normTerm env (If b' m1 (Nil, t), t)) `Union`
                             (normTerm env (If b' m2 (Nil, t), t)), t)
      v@(If _ _ _, _) -> (If b' v (Nil, t), t)
      v -> error $ "unexpected normal form in conditional body in normTerm: " ++
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
      -- ah, the following not necessary because If pushes into records.
      (If cond v1 v2,_) ->
          normTerm env (If cond
                        (Project v1 label, t)
                        (Project v2 label, t), t)
      v@(Var _x, _) -> (Project v label, t)
      v -> error $ "Unexpected normal form in body of Project in normTerm: " ++ 
                    show v
normTerm env (Comp x src body, t) =
    -- Insertion functions for rebuilding a term, dropping a
    -- reconstructor k down through unions and compr'ns (there must be
    -- a better way!).
    let insert k ((v,t) :: TypedTerm) =
            case v of
              Nil -> (Nil, t)
              n1 `Union` n2 -> ((insert k n1) `Union` (insert k n2), t)
              _ -> k (v,t)
        insertFurther k ((v,t) :: TypedTerm) =
            case v of
              Nil -> (Nil, t)
              n1 `Union` n2 -> 
                  ((insertFurther k n1) `Union` (insertFurther k n2), t)
              Comp x m n -> (Comp x m (insertFurther k n), t)
              _ -> k (v,t)
    in case normTerm env src of
      (Nil, _) -> (Nil, t)
      (Singleton src', _) -> 
          forceAndReport (
            let !n' = substTerm x src' body in
            normTerm env (runTyCheck env n')
          ) ("susbtituting "++show src'++" for "++x++" in "++show body)
      (Comp y src2 body2, _) ->
          -- Freshen y-over-src with respect to body (that of the outer
          -- comprehension), because we're widening the scope of y to
          -- include body.
          let (y', body') = if y `elem` fvs body then
                              let y' = minFreeFor body in
                              (y', rename y y' body)
                         else (y, body)
          in
            (normTerm env (Comp y' src2 (Comp x body2 body', t), t))
      (srcL `Union` srcR, _) ->
          ((normTerm env (Comp x srcL body, t)) `Union` 
           (normTerm env (Comp x srcR body, t)), t)
      (tbl @ (Table _tableName fieldTys, _)) ->
          insert (\(v,t) -> (Comp x tbl (v,t), t)) $
                 let env' = Type.bind x ([],TList(TRecord fieldTys)) env in 
                 normTerm env' body
      (If cond src' (Nil, _), _) ->
          assert (x `notElem` fvs cond) $
          let v = normTerm env (Comp x src' body, t) in
          insertFurther (\(v,t) -> (If cond (v,t) (Nil, t), t)) v
      v -> error $
             "unexpected normal form in source part of comprehension: " ++
             show v

-- See (Bird 2010) for a better algorithm here.
minFreeFor :: Term a -> Var
minFreeFor n = head $ variables \\ fvs n 

-- | translateTerm homomorphically translates a normal-form Term to an
-- | SQL Query.
translateTerm :: TypedTerm -> Query
translateTerm (v `Union` u, _) = (translateTerm v) `QUnion` (translateTerm u)
translateTerm (Nil, _)         = Narc.SQL.emptyQuery
translateTerm (f@(Comp _ (Table _ _, _) _, _))                  = translateF f
translateTerm (f@(If _ _ (Nil, _), _))                          = translateF f
translateTerm (f@(Singleton (Record _, _), _))                  = translateF f
translateTerm (f@(Table _ _, _))                                = translateF f
translateTerm x = 
    error $ "translateTerm got unexpected term: " ++ (pretty.fst) x

-- translateF, translateZ and translateB are named after the syntactic
-- classes (in the grammar of the normalized form) which they handle.
-- (F for "for comprehension", Z for "final bit of a nest of
-- comprehensions", and B for "base type"
translateF (Comp x (Table tabname fTys, _) n, _) =
    let q@(Select _ _ _) = translateF n in
    Select {rslt = rslt q,
            tabs = (tabname, x, TRecord fTys):tabs q,
            cond = cond q}
translateF (z@(If _ _ (Nil, _), _))                             = translateZ z
translateF (z@(Singleton (Record _, _), _))                     = translateZ z
translateF (z@(Table _ _, _))                                   = translateZ z
translateF m = error $ "translateF for unexpected term: " ++ pretty (fst m)

translateZ (If b z (Nil, _), _) =
    let q@(Select _ _ _) = translateZ z in
    Select {rslt=rslt q, tabs = tabs q, cond = translateB b : cond q}
translateZ (Singleton (Record fields, _), _) = 
    Select {rslt = QRecord(alistmap translateB fields), tabs = [], cond = []}
translateZ (Table tabname fTys, _) =
    Select {rslt = QRecord[(l,QField tabname l)| (l,_ty) <- fTys],
            tabs = [(tabname, tabname, TRecord fTys)], cond = []}
translateZ z = error$ "translateZ got unexpected term: " ++ (pretty.fst) z

translateB (If b b' b'', _)            = QIf (translateB b)
                                           (translateB b') (translateB b'') 
translateB (Bool n, _)                 = (QBool n)
translateB (Num n, _)                  = (QNum n)
translateB (Project (Var x, _) l, _)   = QField x l
translateB (PrimApp "not" [arg], _)    = QNot (translateB arg)
translateB (PrimApp "<" [l, r], _)     = QOp (translateB l) Less (translateB r)
translateB b = error$ "translateB got unexpected term: " ++ (pretty.fst) b

compile :: TyEnv -> TypedTerm -> Query
compile env = translateTerm . normTerm env

-- Tests

-- -- FIXME: where does this belong? It tests a function internal to this
-- -- module (normTerm) but uses testing apparatus that is defined at a
-- -- "higher" layer (Narc.Test) and uses an otherwise unrelated module
-- -- (Narc.Eval).
-- prop_norm_sound :: TyEnv -> Env -> Property
-- prop_norm_sound tyEnv env =
--   forAll (sized (termGen (dom env))) $ \m ->
--       isErrorMSuccess $ tryErrorGensym $ 
--       do m' <- infer m
--          return (eval env (normTerm tyEnv m') == eval env m')
