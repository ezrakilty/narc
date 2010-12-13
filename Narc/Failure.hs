module Narc.Failure where

import Narc.Debug
import Control.Monad.Error hiding (when, join)
import Gensym

-- Failure and ErrorGensym monads --------------------------------------
-- (TBD: this is more general than Narc; factor it out.)

type Failure a = Either String a

fayl = Left -- TBD: would be better to make Failure a newtype & use
            -- fail from Monad.

-- instance Monad Failure where
--     return = Failure . Right
--     fail = Failure . Left
--     x >>= k = case x of Failure(Left err) -> Failure(Left err)
--                         Failure(Right x') -> k x'

runError :: Either String t -> t
runError (Left e) = breakFlag $ error e
runError (Right x) = x

isError (Left x) = True
isError (Right _) = False

isSuccess (Left _) = False
isSuccess (Right _) = True

type ErrorGensym a = ErrorT String Gensym a

-- | Run an ErrorGensym action, raising errors with `error'.
runErrorGensym = runError . runGensym . runErrorT

-- | Try running an ErrorGensym action, packaging result in an Either
-- | with Left as failure, Right as success.
tryErrorGensym = runGensym . runErrorT

under x = either throwError return x

isErrorMSuccess = either (const False) (const True) 

instance Error () where
    noMsg = ()
    strMsg _ = ()
