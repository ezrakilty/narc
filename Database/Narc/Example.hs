-- | Some example queries demonstrating the Narc interface.

module Database.Narc.Example where

import Test.HUnit
import Database.Narc
import Database.Narc.Embed

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

example5 =
    let employees =
            table "employees" [ ("salary",    TNum)
                              , ("name",      TString)
                              , ("startdate", TNum)
                              ]
    in let highEarners =
           -- employees having salary above 20000
            foreach employees $ \emp ->
            having (primApp "<" [cnst (20000 :: Integer), project emp "salary"]) $
            singleton (record [ ("name", project emp "name"),
                                ("startdate", project emp "startdate") ])

    in let highEarnersFromBefore98 =
            foreach highEarners $ \emp ->
            having (primApp "<" [project emp "startdate", cnst (1998 :: Integer)]) $
            singleton (record [("name", project emp "name")])
    in highEarnersFromBefore98

example6 =
    let employees =
            table "employees" [ ("salary",    TNum)
                              , ("name",      TString)
                              , ("manager",   TString)
                              , ("startdate", TNum)
                              ]
    in let teamOf emp = foreach employees $ \e2 ->
                        having (primApp "==" [e2 ./ "manager", emp ./ "manager"]) $
                        singleton e2
    in let highEarners =
            foreach employees $ \emp ->
            having (primApp "<" [cnst (20000 :: Integer), project emp "salary"]) $
            singleton (record [ ("name", project emp "name"),
                                ("startdate", project emp "startdate") ])

    in let highEarnersFromBefore98 =
            foreach highEarners $ \emp ->
            having (primApp "<" [project emp "startdate", cnst (1998 :: Integer)]) $
            singleton (record [("name", project emp "name")])
    in highEarnersFromBefore98

example_teamRosters = 
  let teamsTable   = table "teams"   [("name", TString), ("id",     TNum)] in
  let playersTable = table "players" [("name", TString), ("teamId", TNum)] in
  let teamRosters = foreach teamsTable $ \t ->
                    singleton (record [("teamName", project t "name"),
                                       ("roster", foreach playersTable $ \p ->
                                                  having (primApp "=" [p ./ "teamId", t ./ "id"]) $
                                                    (singleton (record [("name", (project p "name"))])))])

-- And we can return a list of those teams with at least 9 players as follows:
  in
  let validTeams = foreach teamRosters $ \t ->
                   having (primApp ">=" [(primApp "length" [t ./ "roster"]), cnst (9::Integer)]) $
                   singleton (record [("teamName", project t "teamName")])
                             in validTeams

testx = narcToSQLString nil ~?= "select 0 where false"

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
        ~?= "select _0.name as nom from employees as _0 where \"Joe\" = _0.name"
        ,
        narcToSQLString example5
        ~?= "select _0.name as name from employees as _0 where 20000 < _0.salary and _0.startdate < 1998"
    ]
