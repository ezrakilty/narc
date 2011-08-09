module Database.Narc.TermGen where

import Control.Monad hiding (when)

import Test.QuickCheck hiding (promote, Failure)

import Gensym
import QCUtils

import Database.Narc.AST
import qualified Database.Narc.SQL as SQL
import Database.Narc.Type as Type
import Database.Narc.Util

--
-- QuickCheck term generators ------------------------------------------
--

smallIntGen :: Gen Int
smallIntGen = elements [0..5]

typeGen :: [TyVar] -> Int -> Gen Type
typeGen tyEnv size =
    oneof $ [return TBool,
             return TNum
            ] ++
    [do x <- elements tyEnv; return $ TVar x | length tyEnv > 0] ++
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

-- | Generate a random term, unlikely to be well-typed.
termGen :: [VarName] -> Int -> Gen (Term ())
termGen fvs size = frequency $
    [(1,                    return (Unit, ())),
     (1, do b <- arbitrary; return (Bool b, ())),
     (1, do n <- arbitrary; return (Num n, ()))
    ]
    ++
    (whens (not (null fvs)) [(3, do x <- elements fvs;
                                    return (Var x, ()))])
    ++
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
             tableName <- identGen
             fields <- sequence $ replicate n $
                       do name <- identGen
                          ty <- elements [TBool, TNum]
                          return (name, ty)
             return $ (Table tableName fields, ())),
     (9, do n <- smallIntGen
            fields <- sequence $ replicate n $
                      do name <- identGen
                         term <- termGen fvs (size-1)
                         return (name, term)
            return $ (Record fields, ())),
     (72, do x <- varGen  -- Overwhelmingly favor comprehensions when
                          -- we have enough size remaining, since
                          -- we'll be favoring other stuff when we run
                          -- out of size.
             l <- termGen fvs (size-1)
             m <- termGen (x:fvs) (size-1)
             return $ (Comp x l m, ()))
    ]

closedTermGen :: Int -> Gen (Term' (), ())
closedTermGen size = 
    termGen [] size

oneofMaybe :: [Gen(Maybe a)] -> Gen (Maybe a)
oneofMaybe [] = return Nothing
oneofMaybe (x:xs) = do x' <- x
                       xs' <- oneofMaybe xs
                       case (x', xs') of
                         (Nothing, Nothing) -> return Nothing
                         _ -> oneof (map (return . Just) $ 
                                         asList x' ++ asList xs')

-- Why isn't this bloody thing generating deconstructors??
typedTermGen :: TyEnv -> Type -> Int -> Gen (Term ())
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
          [(2, do fields <- forM fTys $ \(lbl, ty) ->
                              do m <- typedTermGen env ty decSz
                                 return (lbl, m)
                  return $ (Record fields, ()))]
      TList ty ->
          [(2, do m <- typedTermGen env ty decSz 
                  return $ (Singleton m, ()))]
          ++ case ty of 
                TRecord fTys ->
                  if not (and [isBaseTy ty | (_, ty) <- fTys]) then [] else
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

closedTypedTermGen :: Type -> Int -> Gen (Term ())
closedTypedTermGen ty size = 
--    let tyEnv = runErrorGensym makeInitialTyEnv in
    let tyEnv = [] in
    typedTermGen tyEnv ty size

dbTableTypeGen :: Gen Type
dbTableTypeGen = 
    do n <- nonNegInt :: Gen Int
       ty <- elements [TBool, TNum]
       return $ TList (TRecord [('t': show i, ty) | i <- [0..n-1]])


-- Generators

instance Arbitrary SQL.Op where
    arbitrary = oneof [return SQL.Eq, return SQL.Less]

listGen :: Int -> Gen a -> Gen [a]
listGen 0 gen = oneof [ return [], do x <- gen
                                      xs <- listGen 0 gen
                                      return (x : xs)]
listGen n gen = do x <- gen
                   xs <- listGen (n-1) gen
                   return (x : xs)

identCharGen :: Gen Char
identCharGen = oneof $ map return (['a'..'z'] ++ ['A'..'Z'] ++ ['_'])

identGen :: Gen String
identGen = listGen 1 identCharGen

varGen :: Gen String
varGen = (return ('x':)) `ap` identGen

pairGen :: Gen a -> Gen b -> Gen (a, b)
pairGen aGen bGen = do a <- aGen; b <- bGen; return (a, b)
