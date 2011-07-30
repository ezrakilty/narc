{-# LANGUAGE ScopedTypeVariables #-}

module Database.Narc.Debug where

import Prelude hiding (catch)
import Control.Exception (catch, evaluate, throwIO, SomeException)
import Debug.Trace (trace)
import Foreign (unsafePerformIO)

-- | Enable/disable debugging messages
debugFlag :: Bool
debugFlag = False

-- | Trace the given string if debugging is on, or do nothing if not.
debug :: String -> a -> a
debug str = if debugFlag then trace str else id

breakFlag x = x     -- a hook for a breakpoint in GHCi debugger

-- | Force an arbitrary expression, tracing the @String@ arg if
-- forcing produces an exception.
forceAndReport :: a -> String -> a
forceAndReport expr msg = 
          unsafePerformIO $
          catch (evaluate $
                 expr `seq` expr
          ) (\(exc::SomeException) ->
            breakFlag $ 
            debug msg $ 
             Control.Exception.throwIO exc
          )
