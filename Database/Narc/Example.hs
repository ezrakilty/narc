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
            result [ ("name", project emp "name"),
                     ("startdate", project emp "startdate") ]

    in let highEarnersFromBefore98 =
            foreach highEarners $ \emp ->
            having (primApp "<" [project emp "startdate", cnst (1998 :: Integer)]) $
            result [("name", project emp "name")]
    in highEarnersFromBefore98

example6 =
    let employees =
            table "employees" [ ("salary",    TNum)
                              , ("name",      TString)
                              , ("manager",   TString)
                              , ("startdate", TNum)
                              ]
    in let teamOf emp = foreach employees $ \e2 ->
                        having (primApp "=" [e2 ./ "manager", emp ./ "manager"]) $
                        singleton e2
    in let highEarners =
            foreach employees $ \emp ->
            having (primApp "<" [cnst (20000 :: Integer), project emp "salary"]) $
            result [ ("name", project emp "name")
                   , ("startdate", project emp "startdate")
                   , ("manager", project emp "manager")
                   ]

    in let highEarnersFromBefore98 =
            foreach highEarners $ \emp ->
            having (primApp "<" [project emp "startdate", cnst (1998 :: Integer)]) $
            result [ ("name", project emp "name")
                   , ("manager", project emp "manager")
                   ]
    in foreach highEarnersFromBefore98 teamOf

example_teamRosters = 
  let teamsTable   = table "teams"   [("name", TString), ("id",     TNum)] in
  let playersTable = table "players" [("name", TString), ("teamId", TNum)] in
  let rosterFor t = 
          narrowToNames ["name"]
            (filterToFieldValue playersTable "teamId" (t ./ "id"))
  in
  let teamRosters =
          foreach teamsTable $ \t ->
          result [("teamName", project t "name"),
                  ("roster", rosterFor t)]
-- And we can return a list of those teams with at least 9 players as follows:
  in
  let validTeams = foreach teamRosters $ \t ->
                   having (primApp ">=" [(primApp "length" [t ./ "roster"]),
                                         cnst (9::Integer)]) $
                   result [("teamName", project t "teamName")]
  in validTeams

-- | A predicate asserting that the given @field@ of @p@ has the given
-- @value@. @fieldValue field value p@.
fieldValue field value p =
    primApp "=" [p ./ field, value]

-- | Filter to rows which have a particular value in a field:
-- @filterToFieldValue table field value@.
filterToFieldValue table field value =
    filterPred table (fieldValue field value)

-- | Filter to rows which give true for a predicate: @filterPred table pred@.
filterPred table pred =
    foreach table $ \p ->
    having (pred p) $
    singleton p

-- | Project-away all columns but the given ones: @narrowToNames names src@.
narrowToNames names src =
    foreach src $ \p ->
    result [(n, p ./ n) | n <- names]

-- | Take the "first" @n@ elements resulting from @query@. TBD: implement!
takeNarc n query = query

-- | Transform a result set into an ordered result set. TBD: implement!
orderByDesc field query = query

-- | A peculiar query from my train game Perl implementation.
exampleQuery :: Integer -> Integer -> NarcTerm
exampleQuery currentPlayer gameID =
    let playing = table "playing" [("gameID", TNum),
                                   ("player", TNum),
                                   ("position", TNum)] in
    let playingHere = foreach playing $ \p -> 
                      having (primApp "=" [project p "gameID", cnst gameID]) $
                      singleton p in
    takeNarc 1             $ -- TODO: define
    orderByDesc "position" $ -- TODO: define
    (foreach playingHere $ \a ->
     foreach playingHere $ \b ->
     having (primApp "and" [primApp "=" [primApp "+" [project a "position",
                                                       cnst (1::Integer)],
                                          project b "position"],
                            primApp "=" [project a "player", cnst currentPlayer]]) $
     result [("player", project b "player"),
             ("position", project b "position")])
    `union`
    (foreach playingHere $ \a ->
     having (primApp "=" [project a "position", cnst (1::Integer)]) $
     result [("player", project a "player"),
             ("position", project a "position")])
-- The original query: select the player to the right of the current
-- player, or player 1 if there is no current player.

-- select b.player as player, b.position as position
--   from playing a, playing b
--  where a.position + 1 = b.position and a.player = $current_player
-- union
-- select a.player as player, a.position as position
--   from playing a
--  where a.gameID = 1 and a.position = 1
--  order by position desc limit 1

-- How the query compiles:
-- ((select _2.player as player, _2.position as position
--   from playing as _0, playing as _2
--   where _0.gameID = 1 and _2.gameID = 1 and
--       _0.position + 1 = _2.position and _0.player = 1))
-- union
-- ((select _4.player as player, _4.position as position
--   from playing as _4
--   where _4.gameID = 1 and _4.position = 1))

-- | A trivial example.
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
        ,
        narcToSQLString example6
        ~?= "select _3.salary as salary, _3.name as name, _3.manager as manager, _3.startdate as startdate from employees as _0, employees as _3 where 20000 < _0.salary and _0.startdate < 1998 and _3.manager = _0.manager"
        ,
        narcToSQLString example_teamRosters ~?= ""
        ,
        narcToSQLString (exampleQuery 3 4) ~?= ""
    ]
