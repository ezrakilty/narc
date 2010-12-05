{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Narc where

import Prelude hiding (catch)
import Control.Exception (catch, throwIO, evaluate, SomeException)
import Control.Monad.State hiding (when, join)
import Control.Monad.Error (throwError, runErrorT, Error(..))
import List (nub, (\\), sort, sortBy, groupBy, intersperse)
import Maybe (fromJust, isJust, fromMaybe)

import Control.Applicative ((<$>), (<*>))
import Foreign (unsafePerformIO)            -- FIXME

import Test.QuickCheck hiding (promote, Failure)
import QCUtils
import Test.HUnit hiding (State, assert)

import Debug.Trace

import Gensym

import Narc.AST
import Narc.Common
import Narc.Compile
import Narc.Debug
import Narc.Eval
import Narc.Failure
import Narc.Pretty
import Narc.AST.Pretty
import Narc.SQL.Pretty
import Narc.SQL
import Narc.Type as Type
import Narc.TypeInfer
import Narc.Util

evalQuery q = 
    let m' = normTerm [] q in
    let q = compileTerm m' in
    debug ("query is " ++ pretty q) $
    (q,True)

normalizerTests = 
    do initialTyEnv <- makeInitialTyEnv 
       return$ TestList 
                 [TestCase $ unitAssert $ 
                  let term = (Comp "x" (Table "foo" [("fop", TNum)], ())
                              (If (Bool True,())
                               (Singleton (Record
                                           [("f0", (Project (Var "x", ())
                                                    "fop",()))],()),())
                               (Singleton (Record 
                                           [("f0", (Num 3, ()))], ()), ()), 
                               ()), ()) in
                  let tyTerm = runErrorGensym $ infer $ term in
                  groundQuery $ compileTerm $ normTerm initialTyEnv $ tyTerm
                 ]

utests = do normalizerTests <- normalizerTests 
            return $ TestList [tyCheckTests, normalizerTests, typingTest]

unitTest = runErrorGensym $ liftM runTestTT utests

--
-- Big QuickCheck properties
--

prop_eval_safe =
    forAll (sized closedTermGen) $ \m ->
    case runGensym $ runErrorT $ infer m of
      Left _ -> ignore
      Right _ -> label "successful" $
                 let m' = runErrorGensym $ infer m in
                   propertyDefined $
                     (eval initialEnv $! m')

prop_eval_pure_safe = 
    forAll dbTableTypeGen $ \ty ->
    forAll (sized (closedTypedTermGen ty)) $ \m' ->
    let m = m' in
    --debug ("Typechecking " ++ show m) $
    case runGensym $ runErrorT $ infer m of
      Left _ -> label "ill-typed" $ property True
      Right (_, (ty)) -> 
          isDBTableTy ty ==>
          debug ("Trying " ++ (pretty $ fst m)) $
          --collect (numComps m) $ 
                  let m' = runErrorGensym $ infer m in
                  --(eval initialEnv $! m') `seq` 
                  let (q, ok) = (evalQuery $! m') in
                  collect (sizeQuery q) $ 
                          errorAsFalse $
                          ok

-- prop_norm_sound env = eval env . normTerm env == eval env

--
-- QuickCheck term generators ------------------------------------------
--

smallIntGen :: Gen Int
smallIntGen = elements [0..5]

typeGen tyEnv size =
    oneof $ [
         return TBool,
         return TNum
        ] ++
    when (length tyEnv > 0) (do x <- elements tyEnv; return $ TVar x) ++
    whens (size > 0)
        [
         do s <- typeGen tyEnv (size-1)
            t <- typeGen tyEnv (size-1)
            return $ TArr s t,
         do t <- typeGen tyEnv (size-1)
            return $ TList t,
         do n <- smallIntGen :: Gen Int
            fields <- sequence [do t <- typeGen tyEnv (size-1)
                                   return ('f':show i, t) | i <- [0..n]]
            return $ TRecord fields
        ]

termGen fvs size = frequency $
    [(1,                    return (Unit, ())),
     (1, do b <- arbitrary; return (Bool b, ())),
     (1, do n <- arbitrary; return (Num n, ()))
    ] ++
    (whens (not(null(fvs))) [(3, do x <- elements fvs;
                                    return (Var x, ()))]) ++
    whens (size > 0) [
     (3, do x <- varGen
            n <- termGen (x:fvs) (size-1)
            return (Abs x n, ())),
     (6, do m <- termGen fvs (size-1)
            n <- termGen fvs (size-1)
            return $ (App m n, ())),
     (6, do m <- termGen fvs (size-1)
            f <- identGen
            return $ (Project m f, ())),
     (6, do m <- termGen fvs (size-1)
            return $ (Singleton m, ())),
     (18, do n <- smallIntGen
             name <- identGen
             fields <- sequence $ replicate n $
                       do name <- identGen
                          ty <- elements [TBool, TNum]
                          return (name, ty)
             return $ (Table name fields, ())),
     (9, do n <- smallIntGen
            fields <- sequence $ replicate n $
                      do name <- identGen
                         term <- termGen fvs (size-1)
                         return (name, term)
            return $ (Record fields, ())),
     (72, do x <- varGen
             l <- termGen fvs (size-1)
             m <- termGen (x:fvs) (size-1)
             return $ (Comp x l m, ()))
    ]

closedTermGen :: Int -> Gen (Term' (), ())
closedTermGen size = 
--    debug("generating closed term at size " ++ show size) $
    termGen (map fst initialEnv) size

oneofMaybe :: [Gen(Maybe a)] -> Gen (Maybe a)
oneofMaybe [] = return Nothing
oneofMaybe (x:xs) = do x' <- x
                       xs' <- oneofMaybe xs
                       case (x', xs') of
                         (Nothing, Nothing) -> return Nothing
                         _ -> oneof (map (return . Just) $ 
                                         asList x' ++ asList xs')

-- Why isn't this bloody thing generating deconstructors??
typedTermGen :: [(Var, QType)] -> Type -> Int -> Gen (Term ())
typedTermGen env ty sz = 
--    debug ("generating term (type " ++ show ty ++ ") at size " ++ show sz) $
    frequency (
    -- variables
    -- (NOTE: presently only gens vars that have ground type, sans quant'rs)
    [(2, return $ (Var x, ())) | (x, (xQs, xTy)) <- env,
                                 xQs == [] && xTy == ty] ++
    -- constructors
    (case ty of
      TNum  -> [(1, do n <- arbitrary; return (Num n, ()))]
      TBool -> [(1, do b <- arbitrary; return (Bool b, ()))]
      TArr s t -> 
          [(2, do x <- varGen 
                  n <- typedTermGen ((x, ([], s)):(unassoc x env)) t decSz
                  return $ (Abs x n, ()))]
      TRecord fTys -> 
          [(2, do fields <- sequence
                            [do m <- typedTermGen env ty decSz
                                return (lbl, m)
                             | (lbl,ty) <- fTys] :: Gen [(String,Term())]
                  return $ (Record fields, ()))]
      TList ty ->
          [(2, do m <- typedTermGen env ty decSz 
                  return $ (Singleton m, ()))]
          ++ case ty of 
                TRecord fTys ->
                  if not (all (\(_, ty) -> isBaseTy ty) fTys) then [] else
                  [(2, do tab <- identGen
                          return $ (Table ('T':tab) fTys, ()))]
                _ -> []
      _ -> error("Strange type while generating term: " ++ 
                 show ty ++ " (size " ++ show sz ++ ")")
    ) ++
    -- deconstructors
    if (sz <= 0) then [] else (
     [
      (10, do s <- typeGen [] (intSqrt sz)
              m <- typedTermGen env (TArr s ty) decSz
              n <- typedTermGen env s decSz
              return $ (App m n, ())),
      (10, do c <- typedTermGen env TBool decSz
              a <- typedTermGen env ty decSz
              b <- typedTermGen env ty decSz
              return $ (If c a b, ()))
     ] ++
     -- Comprehension: a constructor and a destructor
     case ty of
      (TList _) ->
          [(20, do x <- varGen
                   s <- typeGen [] (intSqrt sz)
                   src <- typedTermGen env (TList s) decSz
                   let env' = Type.bind x ([], s) env
                   body <- typedTermGen env' ty decSz
                   return (Comp x src body, ()))
          ]
      _ -> []
    )
  )
  where decSz = max (sz-1) 0

closedTypedTermGen ty size = 
--    debug("generating closed term at size " ++ show size) $
    let tyEnv = runErrorGensym makeInitialTyEnv in
    typedTermGen tyEnv ty size

dbTableTypeGen :: Gen Type
dbTableTypeGen = 
    do n <- nonNegInt :: Gen Int
       ty <- elements [TBool, TNum]
       return $ TList (TRecord [('t': show i, ty) | i <- [0..n-1]])

prop_typedTermGen_tyCheck =
  forAll (sized $ typeGen []) $ \ty ->
  forAll (sized $ typedTermGen (runErrorGensym makeInitialTyEnv) ty) $ \m ->
  case runGensym $ runErrorT $ infer m of
    Left _ -> False
    Right (m', (ty')) -> errorMToBool $ unify ty ty'

-- Arbitraries

-- instance Arbitrary t => Arbitrary (Maybe t) where
--     arbitrary = oneof [return Nothing,
--                        fmap Just arbitrary]

--
-- QuickCheck Tests
--

-- Generators

instance Arbitrary Op where
    arbitrary = oneof [return Eq, return Less]

listGen :: Int -> Gen a -> Gen [a]
listGen 0 gen = oneof [ return [], do x <- gen
                                      xs <- listGen 0 gen
                                      return (x : xs)]
listGen n gen = do x <- gen
                   xs <- listGen (n-1) gen
                   return (x : xs)

identCharGen :: Gen Char
identCharGen = oneof $ map return (['a'..'z'] ++ ['A'..'Z'] ++ ['_'])

identGen = listGen 1 identCharGen

varGen = (return ('x':)) `ap` identGen

pairGen :: Gen a -> Gen b -> Gen (a, b)
pairGen aGen bGen = do a <- aGen; b <- bGen; return (a, b)


-- THE AWESOME FULL COMPILATION FUNCTION -------------------------------

fullyCompile = compileTerm . normTerm [] . runTyCheck []

-- Main ----------------------------------------------------------------

main = quickCheckWith logSizeArgs prop_eval_pure_safe

-- QuickCheck parameters -----------------------------------------------

sqrtSizeSmallArgs = Args {
    maxSuccess = 100,
    maxDiscard = 100,
    maxSize = 100,
    replay = Nothing
  }

mediumArgs = Args {
    maxSuccess = 1000,
    maxDiscard = 1000,
    maxSize = 500,
    replay = Nothing
  }

logSizeSmallArgs = Args {
    maxSuccess = 100,
    maxDiscard = 100,
    maxSize = 8,
    replay = Nothing
  }

logSizeMedArgs = Args {
    maxSuccess = 1000,
    maxDiscard = 1000,
    maxSize = 12,
    replay = Nothing
  }

logSizeArgs = Args {
    maxSuccess = 10000,
    maxDiscard = 10000,
    maxSize = 16,
    replay = Nothing
  }

-- Builders ------------------------------------------------------------

(!) x = (x, ())

unit = (!)Unit
class Const a where cnst :: a -> Term ()
instance Const Bool where cnst b = (!)(Bool b)
instance Const Integer where cnst n = (!)(Num n)
primApp f args = (!)(PrimApp f args)
var x = (!)(Var x)
abs x body = (!)(Abs x body)
app l m = (!)(App l m)
table tbl ty = (!)(Table tbl ty)
ifthenelse c t f = (!)(If c t f)
singleton x = (!)(Singleton x)
nil = (!)Nil
onion a b = (!)(Union a b)
record fields = (!)(Record fields)
project body field = (!)(Project body field)
foreach src x body = (!)(Comp x src body)

-- Example query -------------------------------------------------------

example_dull = (Comp "x" (Table "foo" [("a", TBool)], ())
                (If (Project (Var "x", ()) "a", ())
                 (Singleton (Var "x", ()), ())
                 (Nil, ()), ()), ())

-- HOAS-ish builders

type HOASTerm = Gensym (Term ()) -- Bleck. Rename.

unit' :: HOASTerm
unit' = return $ (!) Unit

primApp' :: String -> [HOASTerm] -> HOASTerm
primApp' f args =  (!) . PrimApp f <$> sequence args

abs' :: (String -> HOASTerm) -> HOASTerm
abs' fn = do
  n <- gensym
  let x = '_' : show n
  body <- fn x
  return $ (!) $ Abs x body

app' :: HOASTerm -> HOASTerm -> HOASTerm
app' l m = (!) <$> (App <$> l <*> m)

table' tbl ty = return $ (!) $ Table tbl ty

ifthenelse' :: HOASTerm -> HOASTerm -> HOASTerm -> HOASTerm
ifthenelse' c t f = (!) <$> (If <$> c <*> t <*> f)

singleton' :: HOASTerm -> HOASTerm
singleton' x = (!) . Singleton <$> x

nil' :: HOASTerm
nil' = return $ (!) $ Nil

onion' l r = (!) <$> (Union <$> l <*> r)

record' :: [(String, HOASTerm)] -> HOASTerm
record' fields = (!) <$> (Record <$> sequence [do expr' <- expr ; return (lbl, expr') | (lbl, expr) <- fields])

project' :: HOASTerm -> String -> HOASTerm
project' expr field = (!) <$> (Project <$> expr <*> return field)

foreach' :: HOASTerm -> (HOASTerm -> HOASTerm) -> HOASTerm
foreach' src k = do
  src' <- src
  n <- gensym
  let x = '_' : show n
  body' <- k (return (var x))
  return $ (!)(Comp x src' body')


-- Example query -------------------------------------------------------

example' = foreach' (table' "foo" [("a", TBool)]) $ \x -> 
           (ifthenelse' (project' x "a")
            (singleton' x) 
            nil')
