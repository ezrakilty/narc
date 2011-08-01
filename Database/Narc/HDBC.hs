module Database.Narc.HDBC where

import Database.HDBC

import Database.Narc.AST
import Database.Narc.SQL
import Database.Narc.Compile
import Database.Narc.TypeInfer

-- | Run a Narc query directly against an HDBC connection.
run :: IConnection conn => Term a -> conn -> IO [[SqlValue]]
run t conn =
    let sql = serialize (compile [] (runTyCheck [] t)) in
    quickQuery conn sql []

-- FIXME: We need a version of the above that takes a NarcTerm instead
-- of a concrete term.