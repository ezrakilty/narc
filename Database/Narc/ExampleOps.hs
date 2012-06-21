-- | Some example queries demonstrating the Narc interface.

module Database.Narc.Example where

import Prelude hiding ((<), (>), (<=), (>=), (==), (/=), min, max)
import Test.HUnit

import Algebras

import Database.Narc
import Database.Narc.Embed.Ops

example1 = let t = (table "foo" [("a", TBool)]) in
           foreach t $ \x -> 
           (having (x ./ "a")
             (singleton x))

example2 = let t = (table "foo" [("a", TNum)]) in
            let s = (table "bar" [("a", TNum)]) in
            foreach t $ \x -> 
            foreach s $ \y -> 
            ifthenelse (x ./ "a" < y ./ "a")
             (singleton x)
             (singleton y)

example3 =
    let t = table "employees" [("name", TString), ("salary", TNum)] in
    foreach t $ \emp ->
    having (20000 < emp ./ "salary") $
      result [("nom", emp ./ "name")]

example4 =
    let t = table "employees" [("name", TString), ("salary", TNum)] in
    foreach t $ \emp ->
    having (cnst "Joe" /= emp ./ "name") $
      result [("nom", emp ./ "name")]

example5 =
    let employees =
            table "employees" [ ("salary",    TNum)
                              , ("name",      TString)
                              , ("startdate", TNum)
                              ]
    in let query =
            foreach employees $ \emp ->
            having (20000 < emp ./ "salary") $
            result [ ("name", emp ./ "name"),
                     ("startdate", emp ./ "startdate") ]

    in let query2 =
            foreach query $ \emp ->
            having (1998 > emp ./ "startdate") $
            result [("name", emp ./ "name")]
    in query2

-- Unit tests ----------------------------------------------------------

test_example =
    TestList [
        narcToSQLString example1
        ~?= "select _0.a as a from foo as _0 where _0.a"
        ,
        narcToSQLString example2
        ~?= "(select _0.a as a from foo as _0, bar as _1 where _0.a < _1.a) union (select _1.a as a from foo as _0, bar as _1 where not(_0.a < _1.a))"
        ,
        narcToSQLString example3
        ~?= "select _0.name as nom from employees as _0 where 20000 < _0.salary"
        ,
        narcToSQLString example4
        ~?= "select _0.name as nom from employees as _0 where \"Joe\" <> _0.name"
        ,
        narcToSQLString example5
        ~?= "select _0.name as name from employees as _0 where 20000 < _0.salary and 1998 > _0.startdate"
    ]
