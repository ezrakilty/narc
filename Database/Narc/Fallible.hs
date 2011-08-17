{-# LANGUAGE FlexibleContexts #-}
module Database.Narc.Fallible where

import Control.Monad.Error hiding (when, join)
import Gensym
import Database.Narc.Debug

-- Fallible and ErrorGensym monads --------------------------------------
-- (TBD: this is more general than Narc; factor it out.)

data Fallible a = Failure String | Success a
  deriving (Eq, Show)

instance Monad Fallible where
    return = Success
    fail = Failure
    x >>= k = case x of Failure err -> Failure err
                        Success x' -> k x'

runFallible :: Fallible t -> t
runFallible (Failure e) = breakFlag $ error e
runFallible (Success x) = x

fromEither :: Either String a -> Fallible a
fromEither (Left err) = Failure err
fromEither (Right x) = Success x

isError :: Fallible t -> Bool
isError (Failure _) = True
isError (Success _) = False

isSuccess :: Fallible t -> Bool
isSuccess (Failure _) = False
isSuccess (Success _) = True

type FallibleGensym a = ErrorT String Gensym a

-- | Run an ErrorGensym action, raising errors with `error'.
runFallibleGensym :: ErrorT String Gensym a -> a
runFallibleGensym = runFallible . fromEither . runGensym . runErrorT

-- | Try running an ErrorGensym action, packaging result in an Either
-- | with Left as failure, Right as success.
tryFallibleGensym :: ErrorT String Gensym a -> Fallible a
tryFallibleGensym = fromEither . runGensym . runErrorT

fromFallible :: (String -> b) -> (a -> b) -> Fallible a -> b
fromFallible f _g (Failure err) = f err
fromFallible _f g (Success x)   = g x

under :: MonadError String m => Fallible a -> m a
under x = fromFallible throwError return x

instance Error () where
    noMsg = ()
    strMsg _ = ()
