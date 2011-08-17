module Database.Narc.TypeInfer where

import Data.Maybe (fromMaybe)

import Control.Monad.State (lift)

import Test.HUnit

import Gensym
import Database.Narc.AST
import Database.Narc.Type
import Database.Narc.Fallible
import Database.Narc.Debug (debug)
import Database.Narc.Pretty
import Database.Narc.AST.Pretty()

--
-- Type inference ------------------------------------------------------
--

tyCheckTerms :: TyEnv -> [Term a] -> FallibleGensym (TySubst, [TypedTerm])
tyCheckTerms env terms = 
    do results <- sequence [tyCheck env term | term <- terms]
       let (tySubsts, typedTerms) = unzip results
       tySubst <- under $ composeTySubst tySubsts
       return (tySubst, typedTerms)

-- | tyCheck env term infers a type for term in environment env.
-- The environment has type [(Var, QType)];
-- an entry (x, qty) indicates that variable x has the quantified type qty;
-- a QType (ys, ty) indicates the type "forall ys, ty".
tyCheck :: TyEnv -> Term a
        -> FallibleGensym (TySubst, TypedTerm)
tyCheck _env (Unit, _) = 
    do let ty = (TUnit)
       return (emptyTySubst, (Unit, ty))
tyCheck _env (Bool b, _) = 
    do let ty = (TBool)
       return (emptyTySubst, (Bool b, ty))
tyCheck _env (Num n, _) = 
    do let ty = (TNum)
       return (emptyTySubst, (Num n, ty))
tyCheck _env (String s, _) = 
    do let ty = (TString)
       return (emptyTySubst, (String s, ty))
tyCheck _env (Table t tys, _) =
    do let ty = (TList (TRecord tys))
       return (emptyTySubst, (Table t tys, ty))
tyCheck env (Var x, _) =
    do let qTy = fromMaybe (error("Type error: no var " ++ x))
                 $ lookup x env
       ty <- lift $ instantiate qTy
       debug ("*** instantiated " ++ show qTy ++ " to " ++ show ty) $
        return (emptyTySubst, (Var x, (ty)))
tyCheck env (PrimApp fun args, _) = 
    do (tySubst, args') <- tyCheckTerms env args
       return(tySubst, (PrimApp fun args', TBool)) -- TBD
tyCheck env (Abs x n, _) = 
    do argTyVar <- lift gensym
       (tySubst, n'@(_, (nTy))) <- 
           tyCheck ((x, ([], TVar argTyVar)) : env) n
       let argTy = applyTySubst tySubst $ TVar argTyVar
       return(tySubst,
              (Abs x n', (TArr argTy nTy)))
tyCheck env (If c a b, _) =
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
tyCheck _env (Nil, _) = 
    do t <- lift gensym
       return (emptyTySubst, (Nil, (TList (TVar t))))
tyCheck env (Singleton m, _) =
    do (tySubst, m'@(_, (mTy))) <- tyCheck env m
       return (tySubst,
               (Singleton m', (TList mTy)))
tyCheck env (Union a b, _) =
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
    do (tySubst, terms') <- tyCheckTerms env terms
       let fieldTys = map snd terms'
       return (tySubst,
               (Record (zip fieldNames terms'),
                (TRecord [(name, ty)| (ty, name) <- zip fieldTys fieldNames])))
tyCheck env (Project m f, _) =
    do a <- lift gensym
       (tySubst, m'@(_, mTy)) <- tyCheck env m
       case mTy of
         TVar x ->     -- Note: bogus
                return (((x, TRecord [(f, TVar a)]):tySubst),
                        (Project m' f, (TVar a)))
         TRecord fieldTys ->
                case lookup f fieldTys of
                  Nothing -> fail("no field " ++ f ++ " in record " ++ 
                                  show (strip m))
                  Just fieldTy ->
                      return (tySubst,
                              (Project m' f, fieldTy))
         _ -> fail ("Project from non-record type: " ++ pretty (Project m f))
tyCheck env (App m n, _) = 
    do b <- lift gensym;
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

tyCheck env (Comp x src body, _) =
    do (substSrc, src') <- tyCheck env src
       let srcTy = annotation src'
       a <- lift gensym
       srcTySubst <- under $ unify (TList (TVar a)) srcTy
       let srcTy' = applyTySubst srcTySubst (TVar a)
       (substBody, body') <- tyCheck ((x, unquantType srcTy') : env) body
       let bodyTy = annotation body'
       resultSubst <- under $ composeTySubst [substSrc, substBody]
       return (resultSubst, (Comp x src' body', bodyTy))

unquantType :: Type -> QType
unquantType ty = ([], ty)

annotation :: TypedTerm -> Type
annotation (_, ty) = ty

infer :: Term a -> FallibleGensym TypedTerm -- FIXME broken, discards subst'n
infer term =
    do (_, term') <-
        --    runFallibleGensym $ 
               tyCheck [] term
       return term'

infer' :: Term' a -> FallibleGensym TypedTerm
infer' term = infer (term, undefined)

runInfer :: Term a -> TypedTerm
runInfer = runFallibleGensym . infer

typeAnnotate :: TyEnv -> Term a -> FallibleGensym (Term Type)
typeAnnotate env m =
    do (subst, m') <- tyCheck env m
       return $ retagulate (applyTySubst subst . snd) m'

runTyCheck :: [(VarName, QType)] -> Term a -> TypedTerm
runTyCheck env m = runFallibleGensym $ typeAnnotate env m

tryTyCheck :: [(VarName, QType)] -> Term a -> Fallible TypedTerm
tryTyCheck env m = tryFallibleGensym $ typeAnnotate env m

inferTys :: Term () -> FallibleGensym Type
inferTys m = 
    do (_, (ty)) <- infer m
       return (ty)

inferType :: Term () -> FallibleGensym Type
inferType m = infer m >>= (return . snd)

runInferType :: Term () -> Type
runInferType = runFallibleGensym . inferType

inferType' :: Term' () -> FallibleGensym Type
inferType' m = infer' m >>= (return . snd)

-- UNIT TESTS ----------------------------------------------------------

unitAssert :: Bool -> Assertion
unitAssert b = assertEqual "." b True

tyCheckTests :: Test
tyCheckTests =
    TestList ["Simple application of id to table" ~:
                     (runFallibleGensym $ 
                       inferTys (App (Abs "x" (Var "x", ()), ())
                              (Table "wine" [], ()), ()))
                       ~?= (TList (TRecord [])),
              "Curried application of id to table" ~:
                     (runFallibleGensym . inferTys)
                     (App (App
                              (Abs "x" (Abs "y" (App (Var "x", ())
                                                     (Var "y", ()), ()), ()), ())
                                 (Abs "x" (Var "x", ()), ()), ())
                                 (Table "wine" [], ()), ())
                       ~?= (TList (TRecord [])),
              "Curried application, de/reconstructing record" ~:
                     (runFallibleGensym . inferTys) 
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
                      (tryFallibleGensym . inferType)
                      (Abs "x" (App (Var "x", ()) (Var "x", ()), ()), ())
                  ]

typingTest1 :: (Type, TySubst, Bool)
typingTest1 = 
  let idTy = (TArr (TVar 9) (TVar 9)) in
  let concatMapTy = (TArr (TArr (TVar 2) (TList (TVar 3)))
                     (TArr (TList (TVar 2))
                               (TList (TVar 3)))) in
  let Success mArrSubst = unify concatMapTy  (TArr (TVar 4) (TVar 5)) in
  let argTy = applyTySubst mArrSubst (TVar 4) in
             -- TArr (TVar 2) ([],Just 0) (TList (TVar 3))
  let Success funcArgSubst = unify argTy idTy in
  let resultTy = (applyTySubst funcArgSubst $ applyTySubst mArrSubst (TVar 5)) 
  in
  (resultTy, funcArgSubst,
   case resultTy of
   TArr (TList (TList (TVar a))) (TList (TVar b)) -> a == b
   _ -> False    -- unexpected form of result!
  )

typingTest :: Test
typingTest = let (_,_,x) = typingTest1 in 
             TestCase (unitAssert x)
