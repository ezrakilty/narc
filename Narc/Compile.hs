{-# LANGUAGE ScopedTypeVariables #-}

module Narc.Compile where

import Control.Exception (evaluate, throwIO) -- FIXME: Used just for debugging? Eliminate.

import Data.List ((\\))

import Narc.AST
import Narc.Contract
import Narc.Debug (debug, forceAndReport)
import Narc.Type as Type
import Narc.TypeInfer
import Narc.Util (image, maps, alistmap)
import Narc.Pretty
import Narc.AST.Pretty
import Narc.SQL.Pretty
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
normTerm env (m@(Unit, _)) = m
normTerm env (m@(Bool b, _)) = m
normTerm env (m@(Num n, _)) = m
normTerm env (PrimApp fun args, t) = (PrimApp fun (map (normTerm env) args), t)
normTerm env (expr@(Var x, t)) = 
    -- Eta-expand at record type.
    if x `maps` env then 
        case t of
          TRecord t -> etaExpand expr t
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
      v -> error $ "unexpected normal form in appl posn in normTerm" ++ show v
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
      m@(If _ _ _, _) -> (If b' m (Nil, t), t)
      v -> error $ "unexpected normal form in conditional body in normTerm: " ++
                    show v
normTerm env (If b@(_,bTy) m n, t@(TList _)) = -- n /= Nil
    ((normTerm env (If b m (Nil, t), t)) `Union` 
     (normTerm env (If (PrimApp "not" [b], bTy) m (Nil, t), t)), t)
normTerm env (If b m n, t@(TRecord fTys)) =
    let b' = normTerm env b in
    let (Record mFields, _) = normTerm env m
        (Record nFields, _) = normTerm env n in
    (Record[(l, (If b' (image l mFields) (image l nFields), (image l fTys)))
            | (l, _) <- mFields],
     t)
normTerm env (If b m n, t) = 
    (If (normTerm env b) (normTerm env m) (normTerm env n), t)
normTerm env (Singleton m, t) = (Singleton (normTerm env m), t)
normTerm env (Nil, t) = (Nil, t)
normTerm env (m `Union` n, t) = ((normTerm env m) `Union` (normTerm env n), t)
normTerm env (Record fields, t) =
    (Record [(a, normTerm env m) | (a, m) <- fields], t)
normTerm env (Project m a, t) = 
    case normTerm env m of
      (Record fields, _) -> case (lookup a fields) of 
                              Just x -> x ; Nothing -> error$"no field " ++ a
      -- ah, the following not necessary because if pushes into records.
      (If b m' n',_)-> normTerm env (If b (Project m' a, t) (Project n' a, t), t)
      (m@(Var x, t)) -> (Project m a, t)
      v -> error $ "Unexpected normal form in body of Project in normTerm: " ++ 
                    show v
normTerm env (Comp x m n, t) =
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
    in case normTerm env m of
      (Nil, _) -> (Nil, t)
      (Singleton m', _) -> 
          forceAndReport (
            let !n' = substTerm x m' n in
            normTerm env (runTyCheck env n')
          ) ("susbtituting "++show m'++" for "++x++" in "++show n)
      (Comp y l' m', s) ->
          let (y', n') = if y `elem` fvs n then
                             let y' = head $ variables \\ fvs n in
                             (y', rename y y' n)
                         else (y, n) 
          in
            (normTerm env (Comp y' l' (Comp x m' n', t), t))
      (m1 `Union` m2, _) ->
          ((normTerm env (Comp x m1 n, t)) `Union` 
           (normTerm env (Comp x m2 n, t)), t)
      (tbl @ (Table s fTys, _)) ->
          insert (\(v,t) -> (Comp x tbl (v,t), t)) $
                 let env' = Type.bind x ([],TList(TRecord fTys)) env in 
                 normTerm env' n
      (If b m' (Nil, _), _) ->
          assert (x `notElem` fvs b) $
          let v = normTerm env (Comp x m' n, t) in
          insertFurther (\(v,t) -> (If b (v,t) (Nil, t), t)) v
--           insert  (\(v,t) -> (Comp x m' (v,t), t)) $
--             insertFurther (\(v,t) -> (If b (v,t) (Nil, t), t)) (normTerm env n)
      v -> error$ "unexpected normal form in source of comprehension: " ++ show v

-- | compileTerm homomorphically translates a normal-form Term to an SQL Query.
compileTerm :: TypedTerm -> Query
compileTerm (v `Union` u, _) = (compileTerm v) `QUnion` (compileTerm u)
compileTerm (Nil, _) = Select {rslt=QRecord[],tabs=[],cond=[QBool False]}
compileTerm (f@(Comp x (Table tabname fTys, _) n, _))               = compileF f
compileTerm (f@(If b z (Nil, _), _))                                = compileF f
compileTerm (f@(Singleton (Record fields, _), _))                   = compileF f
compileTerm (f@(Table tabname fTys, _))                             = compileF f
compileTerm x = 
    error $ "compileTerm got unexpected term: " ++ (pretty.fst) x

compileF (Comp x (Table tabname fTys, _) n, _) =
    let q@(Select _ _ _) = compileF n in
    Select {rslt=rslt q, tabs = (tabname, x, TRecord fTys):tabs q, cond = cond q}
compileF (z@(If _ _ (Nil, _), _))                                   = compileZ z
compileF (z@(Singleton (Record fields, _), _))                      = compileZ z
compileF (z@(Table tabname fTys, _))                                = compileZ z

compileZ (If b z (Nil, _), _) =
    let q@(Select _ _ _) = compileZ z in
    Select {rslt=rslt q, tabs = tabs q, cond = compileB b : cond q}
compileZ (Singleton (Record fields, _), _) = 
    Select {rslt = QRecord(alistmap compileB fields), tabs = [], cond = []}
compileZ (Table tabname fTys, _) =
    Select {rslt = QRecord[(l,QField tabname l)| (l,ty) <- fTys],
            tabs = [(tabname, tabname, TRecord fTys)], cond = []}
compileZ z = error$ "compileZ got unexpected term: " ++ (pretty.fst) z

compileB (If b b' b'', _)        = QIf (compileB b) (compileB b') (compileB b'') 
compileB (Bool n, _)                 = (QBool n)
compileB (Num n, _)                  = (QNum n)
compileB (Project (Var x, _) l, _)   = QField x l
compileB (PrimApp "not" [arg], _)    = QNot (compileB arg)
compileB b = error$ "compileB got unexpected term: " ++ (pretty.fst) b
