{-# LANGUAGE ScopedTypeVariables #-}

module Database.Narc.Type where

import Test.QuickCheck

import Gensym
import QCUtils

import Data.List ((\\))
import Control.Monad.State (State(..), get, put, evalState) -- TBD: use Gensym monad instead
import Control.Applicative ((<$>))
import Database.Narc.Failure (Failure, fayl)
import Database.Narc.Failure.QuickCheck
import Database.Narc.Util (dom, rng, image, alistmap, sortAlist, onCorresponding,
                     disjointAlist, validEnv, eqUpTo)
import Database.Narc.Var

type TyVar = Int

data Type = TBool | TNum | TString | TUnit | TList Type
          | TArr Type Type
          | TRecord [(String, Type)]
          | TVar TyVar
    deriving (Eq, Show)

type QType = ([TyVar], Type)

type TySubst = [(Int, Type)]

type TyEnv = [(Var, QType)]

-- Operations on types, rows and substitutions ------------------------

isBaseTy TBool = True
isBaseTy TNum  = True
isBaseTy TString  = True
isBaseTy _     = False

isTyVar (TVar _) = True
isTyVar _        = False

isDBRecordTy (TRecord fields) = all (isBaseTy . snd) fields
isDBRecordTy _                = False

isRecordTy (TRecord fields) = True
isRecordTy _                = False

isDBTableTy (TList ty) = isDBRecordTy ty
isDBTableTy _          = False

emptyTySubst :: (TySubst)
emptyTySubst = ([])

-- | ftvs: free type variables
ftvs TBool = []
ftvs TNum = []
ftvs TString = []
ftvs TUnit = []
ftvs (TList t) = ftvs t
ftvs (TArr s t) = ftvs s ++ ftvs t
ftvs (TRecord fields) = concat [ftvs t | (lbl, t) <- fields]
ftvs (TVar a) = [a]

numFtvs = length . ftvs

-- | ftvsSubst: the free type variables of a type substitution--that is,
-- the type variables free in the types in the range of the substitution.
ftvsSubst a = concatMap ftvs $ rng a

-- | occurs x ty: does variable x appear in type ty? (Note there are no
-- type-variable binders).
occurs x (TVar y) | x == y    = True
                  | otherwise = False
occurs x (TArr s t) = x `occurs` s || x `occurs` t
occurs x (TList t) = x `occurs` t
occurs x (TRecord t) = any (occurs x) (map snd t)
occurs x (TUnit) = False
occurs x (TBool) = False
occurs x (TNum) = False
occurs x (TString) = False

applyTySubst :: TySubst -> Type -> Type
applyTySubst subst (TUnit) = TUnit
applyTySubst subst (TBool) = TBool
applyTySubst subst (TNum) = TNum
applyTySubst subst (TString) = TString
applyTySubst subst (TVar a) = case lookup a subst of
                              Nothing -> TVar a
                              Just ty -> ty
applyTySubst subst (TArr a b) =
    TArr (applyTySubst subst a) (applyTySubst subst b)
applyTySubst subst (TList a) = TList (applyTySubst subst a)
applyTySubst subst (TRecord a) = TRecord (alistmap (applyTySubst subst) a)


-- Type operations -----------------------------------------------------

instantiate (qs, ty) =
    do subst <- sequence [do y <- gensym ; return (q, TVar y) | q <- qs]
       return $ applyTySubst subst ty

{- | normalizeType:
   Renumber all the type variables in a normal way to allow
   comparing types.
-}
normalizeType :: Type -> State (Int, [(Int, Int)]) Type
normalizeType TBool = return TBool
normalizeType TNum = return TNum
normalizeType TString = return TString
normalizeType TUnit = return TUnit
normalizeType (TList ty) = TList <$> normalizeType ty
normalizeType (TRecord recTy) = undefined
normalizeType (TVar a) = do (ctr, env) <- Control.Monad.State.get
                            case lookup a env of
                              Nothing -> do put (ctr+1, (a, ctr):env)
                                            return $ TVar ctr
                              Just b -> return $ TVar b
normalizeType (TArr s t) =
    do s' <- normalizeType s
       t' <- normalizeType t
       return $ TArr s' t'

runNormalizeType ty = evalState (normalizeType ty) (0, [])

-- instanceOf: is there a substitution that turns ty2 into ty1? Useful in tests
instanceOf :: Type -> Type -> Failure ()
instanceOf ty1 (TVar x) = return ()
instanceOf TBool TBool = return ()
instanceOf TNum TNum = return ()
instanceOf TString TString = return ()
instanceOf (TArr s t) (TArr u v) = 
    instanceOf t v >>
    instanceOf s u
instanceOf (TList a) (TList b) = instanceOf a b
instanceOf (TRecord a) (TRecord b) = 
    let a' = sortAlist a 
        b' = sortAlist b
    in
      do result <- sequence [if ax == bx then instanceOf ay by else fayl "Record mismatch"
                             | ((ax, ay), (bx, by)) <- zip a' b']
         return ()
instanceOf a b = fayl ""

unify :: Type -> Type -> Failure (TySubst)
unify s t | s == t = return ([])
unify (TVar x) t | not (x `occurs` t) = return ([(x, t)])
                 | otherwise = fayl("Occurs check failed on " ++ 
                                    show (TVar x) ++ " and " ++ show t)
unify t (TVar x) | not (x `occurs` t) = return ([(x, t)])
                 | otherwise = fayl("Occurs check failed on " ++ 
                                    show t ++ " and " ++ show (TVar x))
unify TBool TBool = return ([])
unify TNum TNum = return ([])
unify TString TString = return ([])
unify (TArr s t) (TArr u v) = 
    do substSU <- unify s u
       substTV <- unify (applyTySubst substSU t)
                        (applyTySubst substSU v)
       composeTySubst [substTV, substSU]
unify (TList a) (TList b) = unify a b
unify (TRecord a) (TRecord b) = 
    let a' = sortAlist a 
        b' = sortAlist b
    in
      do substs <- sequence
                [if ax == bx then unify ay by else
                     fayl ("Record types " ++ show a' ++ 
                           " and " ++ show b' ++ 
                           " mismatched.")
                 | ((ax, ay), (bx, by)) <- zip a' b']
         let (tySubsts) = substs
         subst <- composeTySubst tySubsts
         return (subst)
unify a b = fayl("Type mismatch between " ++ 
                 show a ++ " and " ++ show b)

unifyAll :: [Type] -> Failure TySubst
unifyAll [] = return ([])
unifyAll [x] = return ([])
unifyAll (x1:x2:xs) = do (tySubst) <- x1 `unify` x2
                         unifyAll (map (applyTySubst tySubst)
                                   (x2:xs))

composeTySubst :: [TySubst] -> Failure TySubst
composeTySubst [] = return $ ([])
composeTySubst subst =
    let (tySubsts) = subst in
    do addlSubsts <- sequence $
                         onCorresponding unifyAll $ concat tySubsts
       let (addlTySubsts) = addlSubsts
       let substs' = tySubsts ++ addlTySubsts
       let tySubst = flip foldr1 substs'
                 (\s1 s2 -> s1 ++ alistmap (applyTySubst s1) s2)
       if any (\(a,b) -> occurs a b) tySubst then 
          fayl "Circular type substitution in composeTySubst" 
        else 
            return (tySubst)

prop_composeTySubst = 
    forAll (genEnv 0) $ \a ->
    forAll (genEnv (length a)) $ \b ->
    forAll arbitrary $ \ty ->
    disjointAlist a b && validEnv a && validEnv b ==>
    (do ab <- composeTySubst[a, b]
        return $ applyTySubst ab ty)
    == (return $ (applyTySubst a $ applyTySubst b ty) :: Failure Type)

-- unused
disjoinSubst :: TySubst -> TySubst -> TySubst
disjoinSubst a b =
  [(image bx mapping, applyTySubst subst by) | (bx, by) <- b]
    where mapping = (dom b ++ ftvsSubst b) `zip`
                      ([0..] \\ (dom a ++ ftvsSubst a))
          subst = alistmap TVar mapping

instance Arbitrary Type where
    arbitrary = 
        oneof
          [ return TBool
          , return TNum
          , return TString
          , do s <- arbitrary
               t <- arbitrary
               return (TArr s t)
          , do x <- posInt
               return (TVar x)
          ]

-- Check that unification produces a substitution which actually
-- unifies the two types. (Currently fails; something wrong with the way
-- substitutions are composed or not.)
prop_unify_apply_subst = 
  forAll arbitrary $ \(a :: Type) ->
  forAll arbitrary $ \(b :: Type) -> 
    collect (numFtvs a, numFtvs b) $
    failureToPropertyIgnoreFailure $
    do (subst) <- a `unify` b
       let e = applyTySubst subst a
       let f = applyTySubst subst b
       return $ eqUpTo runNormalizeType e f

-- { Typing environments } ---------------------------------------------

bind x v env = (x,v):env
