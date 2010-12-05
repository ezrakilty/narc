{-# LANGUAGE ScopedTypeVariables #-}

module Narc.Debug where

import Prelude hiding (catch)
import Control.Exception (catch, evaluate, throwIO, SomeException)
import Debug.Trace (trace)
import Foreign (unsafePerformIO)

-- Debugging utilities

debugFlag =         -- enable/disable debugging messages
    False

breakFlag x = x     -- a hook for a breakpoint in GHCi debugger

debug str = if debugFlag then trace str else id

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
