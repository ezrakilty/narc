module Database.Narc.TypeInfer where

import Data.Maybe (fromMaybe)
import Data.Either

import Control.Monad.State (lift)

import Test.HUnit

import Gensym
import Database.Narc.AST
import Database.Narc.Type
import Database.Narc.Failure
import Database.Narc.Debug (debug)
import Database.Narc.Pretty

import Database.Narc.AST.Pretty
--
-- Type inference ------------------------------------------------------
--

tyCheckTerms env terms = 
    do results <- sequence [tyCheck env term | term <- terms]
       let (tySubsts, terms') = unzip results
       let (terms'', termTys) = unzip terms'
       tySubst <- under $ composeTySubst tySubsts
       return (tySubst, terms')

-- | tyCheck env term infers a type for term in environment env.
-- The environment has type [(Var, QType)];
-- an entry (x, qty) indicates that variable x has the quantified type qty;
-- a QType (ys, ty) indicates the type "forall ys, ty".
tyCheck :: TyEnv -> Term a
        -> ErrorGensym (TySubst, Term Type)
tyCheck env (Unit, _) = 
    do let ty = (TUnit)
       return (emptyTySubst, (Unit, ty))
tyCheck env (Bool b, _) = 
    do let ty = (TBool)
       return (emptyTySubst, (Bool b, ty))
tyCheck env (Num n, _) = 
    do let ty = (TNum)
       return (emptyTySubst, (Num n, ty))
tyCheck env (String s, _) = 
    do let ty = (TString)
       return (emptyTySubst, (String s, ty))
tyCheck env (Table t tys, _) =
    do let ty = (TList (TRecord tys))
       return (emptyTySubst, (Table t tys, ty))
tyCheck env (Var x, _) =
    do let qTy = fromMaybe (error("Type error: no var " ++ x))
                 $ lookup x env
       ty <- lift $ instantiate qTy
       debug ("*** instantiated " ++ show qTy ++ " to " ++ show ty) $
        return (emptyTySubst, (Var x, (ty)))
tyCheck env (PrimApp fun args, _) = 
    do (tySubst, args) <- tyCheckTerms env args
       return(tySubst, (PrimApp fun args, (TBool))) -- TBD
tyCheck env (Abs x n, _) = 
    do argTyVar <- lift gensym
       (tySubst, n'@(_, (nTy))) <- 
           tyCheck ((x, ([], TVar argTyVar)) : env) n
       let argTy = applyTySubst tySubst $ TVar argTyVar
       return(tySubst,
              (Abs x n', (TArr argTy nTy)))
tyCheck env (term@(If c a b, _)) =
    do (cTySubst, c'@(_, (cTy))) <- tyCheck env c
       (aTySubst, a'@(_, (aTy))) <- tyCheck env a
       (bTySubst, b'@(_, (bTy))) <- tyCheck env b
       cBaseTySubst <- under (unify cTy TBool)
       abTySubst <- under $ unify aTy bTy
       tySubst <- under $ composeTySubst
                             [aTySubst, bTySubst, cTySubst,
                              cBaseTySubst, abTySubst]
       let ty = applyTySubst tySubst bTy
       return (tySubst,
               (If c' a' b', (ty)))
tyCheck env (Nil, _) = 
    do t <- lift gensym
       return (emptyTySubst, (Nil, (TList (TVar t))))
tyCheck env (Singleton m, _) =
    do (tySubst, m'@(_, (mTy))) <- tyCheck env m
       return (tySubst,
               (Singleton m', (TList mTy)))
tyCheck env (term@(Union a b, _)) =
    do (aTySubst, a'@(_, (aTy))) <- tyCheck env a
       (bTySubst, b'@(_, (bTy))) <- tyCheck env b
       abTySubst <- under $ unify aTy bTy
       tySubst <- under $ composeTySubst
                             [aTySubst, bTySubst, abTySubst]
       let ty = applyTySubst tySubst bTy
       return (tySubst,
               (Union a' b', (ty)))
tyCheck env (Record fields, _) =
    let (fieldNames, terms) = unzip fields in
    do (tySubst, terms) <- tyCheckTerms env terms
       let fieldTys = map snd terms
       return (tySubst,
               (Record (zip fieldNames terms),
                (TRecord [(name,ty)| (ty, name) <- zip fieldTys fieldNames])))
tyCheck env (term@(Project m f, _)) =
    do rowVar <- lift gensym; a <- lift gensym
       (tySubst, m'@(_, mTy)) <- tyCheck env m
       case mTy of
         TVar x ->     -- Note: bogus
                return (((x, TRecord [(f, TVar a)]):tySubst),
                        (Project m' f, (TVar a)))
         TRecord fieldTys ->
                case lookup f fieldTys of
                  Nothing -> fail("no field " ++ f ++ " in record " ++ 
                                  pretty (strip m))
                  Just fieldTy ->
                      return (tySubst,
                              (Project m' f, fieldTy))
         _ -> fail("Type error: projection of field '" ++ f ++
                   "' from non-record type " ++ pretty mTy ++
                   " in term " ++ pretty (strip term) ++ ".")
tyCheck env (App m n, _) = 
    do a <- lift gensym; b <- lift gensym;
       (mTySubst, m'@(_, (mTy))) <- tyCheck env m
       (nTySubst, n'@(_, (nTy))) <- tyCheck env n
       let nTy' = applyTySubst mTySubst $ nTy
       let mTy' = applyTySubst nTySubst $ mTy
       subExprTySubst <- under $ composeTySubst [mTySubst, nTySubst]
       
       let mArrTy = TArr (nTy') (TVar b)
       mArrTySubst <- under $ unify mArrTy mTy'
       
       let resultTy = applyTySubst mArrTySubst $ TVar b
       
       tySubst <- under $ composeTySubst [mArrTySubst,
                                          subExprTySubst]
       
       return (tySubst,
               (App m' n', (resultTy)))

tyCheck env term@(Comp x src body, d) =
    do (substSrc, src') <- tyCheck env src
       let srcTy = typeAnno src'
       a <- lift gensym
       srcTySubst <- under $ unify (TList (TVar a)) srcTy
       let srcTy' = applyTySubst srcTySubst (TVar a)
       (substBody, body') <- tyCheck ((x, unquantType srcTy') : env) body
       let bodyTy = typeAnno body'
       resultSubst <- under $ composeTySubst [substSrc, substBody]
       return (resultSubst, (Comp x src' body', bodyTy))

unquantType :: Type -> QType
unquantType ty = ([], ty)

typeAnno :: Term Type -> Type
typeAnno (_, ty) = ty

makeInitialTyEnv :: ErrorGensym [(String, QType)]
makeInitialTyEnv = return []

infer :: Term a -> ErrorGensym TypedTerm -- FIXME broken, discards subst'n
infer term =
    do initialTyEnv <- makeInitialTyEnv
       (_, term') <-
        --    runErrorGensym $ 
               tyCheck initialTyEnv term
       return term'

infer' :: Term' a -> ErrorGensym TypedTerm
infer' term = infer (term, undefined)

runInfer = runErrorGensym . infer

runTyCheck env m = runErrorGensym $ 
    do initialTyEnv <- makeInitialTyEnv
       (subst, m') <- tyCheck (initialTyEnv ++ env) m
       return $ retagulate (applyTySubst subst . snd) m'

inferTys :: Term () -> ErrorGensym Type
inferTys m = 
    do (_, (ty)) <- infer m
       return (ty)

inferType :: Term () -> ErrorGensym Type
inferType m = infer m >>= (return . snd)

runInferType = runErrorGensym . inferType

inferType' :: Term' () -> ErrorGensym Type
inferType' m = infer' m >>= (return . snd)

-- UNIT TESTS ----------------------------------------------------------

unitAssert b = assertEqual "." b True

tyCheckTests =
    TestList ["Simple application of id to table" ~:
                     (runErrorGensym $ 
                       inferTys (App (Abs "x" (Var "x", ()), ())
                              (Table "wine" [], ()), ()))
                       ~?= (TList (TRecord [])),
              "Curried application of id to table" ~:
                     (runErrorGensym . inferTys)
                     (App (App
                              (Abs "x" (Abs "y" (App (Var "x", ())
                                                     (Var "y", ()), ()), ()), ())
                                 (Abs "x" (Var "x", ()), ()), ())
                                 (Table "wine" [], ()), ())
                       ~?= (TList (TRecord [])),
              "Curried application, de/reconstructing record" ~:
                     (runErrorGensym . inferTys) 
                     (App (App
                      (Abs "f" (Abs "x" (App (Var "f",()) (Var "x",()),()),()),())
                      (Abs "x"
                       (Record[("baz", (Project(Var "x",()) "foo", ()))],
                        ()),
                       ()), ())
                      (Record [("foo", (Num 47, ()))], ()), ())
                      ~?= (TRecord[("baz", TNum)]),
              "omega" ~:
                    unitAssert $ isError $
                      (tryErrorGensym . inferType)
                      (Abs "x" (App (Var "x", ()) (Var "x", ()), ()), ())
                  ]

typingTest1 = 
  let idTy = (TArr (TVar 9) (TVar 9)) in
  let concatMapTy = (TArr (TArr (TVar 2) (TList (TVar 3)))
                     (TArr (TList (TVar 2))
                               (TList (TVar 3)))) in
  let Right mArrSubst = unify concatMapTy  (TArr (TVar 4) (TVar 5)) in
  let argTy = applyTySubst mArrSubst (TVar 4) in
             -- TArr (TVar 2) ([],Just 0) (TList (TVar 3))
  let Right funcArgSubst = unify argTy idTy in
  let resultTy = (applyTySubst funcArgSubst $ applyTySubst mArrSubst (TVar 5)) 
  in
  (resultTy, funcArgSubst,
   case resultTy of
   TArr (TList (TList (TVar a))) (TList (TVar b)) -> a == b)

typingTest = let (_,_,x) = typingTest1 in 
             TestCase (unitAssert x)
