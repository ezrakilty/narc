-- | Some example queries demonstrating the Narc interface.

module Database.Narc.Example where

import Test.HUnit
import Database.Narc

example1 = let t = (table "foo" [("a", TBool)]) in
           foreach t $ \x -> 
           (having (project x "a")
             (singleton x))

example2 = let t = (table "foo" [("a", TNum)]) in
            let s = (table "bar" [("a", TNum)]) in
            foreach t $ \x -> 
            foreach s $ \y -> 
            ifthenelse (primApp "<" [project x "a", project y "a"])
             (singleton x)
             (singleton y)

example3 =
    let t = table "employees" [("name", TString), ("salary", TNum)] in
    foreach t $ \emp ->
    having (primApp "<" [cnst (20000::Integer), project emp "salary"]) $
      result [("nom", project emp "name")]

example4 =
    let t = table "employees" [("name", TString), ("salary", TNum)] in
    foreach t $ \emp ->
    having (primApp "=" [cnst "Joe", project emp "name"]) $
      result [("nom", project emp "name")]

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
        ~?= "select _0.name as nom from employees as _0 where 20000 < _0.salary",
        narcToSQLString example4
        ~?= "select _0.name as nom from employees as _0 where \"Joe\" = _0.name"
    ]
