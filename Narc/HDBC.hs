module Narc.HDBC where

import Database.HDBC

import Narc.AST
import Narc.SQL
import Narc.Compile
import Narc.TypeInfer

run :: IConnection conn => Term a -> conn -> IO [[SqlValue]]
run t conn =
    let sql = serialize (compile [] (runTyCheck [] t)) in
    quickQuery conn sql []
