module Narc.Util where

import Data.Maybe (fromJust, isJust)
import Data.List as List ((\\), nub, intersperse, groupBy, sortBy, sort)

--
-- List Utilities
--

dom alist = map fst alist
rng alist = map snd alist

collate proj = groupBy (\x y -> proj x == proj y) . 
               sortBy (\x y -> proj x `compare` proj y)

sortAlist :: [(String, b)] -> [(String, b)]
sortAlist = sortBy (\a b -> fst a `compare` fst b)

cross f g (x,y) = (f x, g y)

onRight f = cross id f
onLeft f = cross f id

-- | shadow: given two alists, return the elements of the first that
-- are NOT mapped by the second
shadow as bs = [(a,x) | (a,x) <- as, a `notElem` domBs]
    where domBs = map fst bs

-- | Tests that an alist or environment is well-formed: that its first
-- | components are all unique.
validEnv xs = length (nub $ map fst xs) == length xs

mr agg xs = map reduceGroup (collate fst xs)
    where reduceGroup xs = let (as, bs) = unzip xs in
                             (the as, agg bs)
          the xs | allEq xs = head xs

onCorresponding :: Ord a => ([b]->c) -> [(a,b)] -> [c]
onCorresponding agg xs = map reduceGroup (collate fst xs)
    where reduceGroup xs = agg $ map snd xs

($>) x f = f x

image x = fromJust . lookup x

maps x = isJust . lookup x

intSqrt :: Integral a => a -> a
intSqrt = floor . sqrt . fromIntegral

unassoc a = filter ((/= a) . fst)

nubassoc [] = []
nubassoc ((x,y):xys) = (x,y) : (nubassoc $ unassoc x xys)

graph f xs = [(x, f x) | x <- xs]
alistmap f = map (\(a, b) -> (a, f b))

bagEq a b = a \\ b == [] && b \\ a == []

setEq a b = (nub a) `bagEq` (nub b)

u a b = nub (a ++ b)

union lists = nub $ concat lists

contains a b = null(b \\ a)

setMinus xs ys = nub $ sort $ xs \\ ys

(\\\) xs ys = setMinus xs ys

allEq [] = True
allEq (x:xs) = all (== x) xs

disjoint :: Eq a => [a] -> [a] -> Bool
disjoint xs ys = not (any (\x-> any (==x) ys) xs)

disjointAlist xs ys = disjoint (map fst xs) (map fst ys)
-- disjointAlist [] _ = True
-- disjointAlist _ [] = True
-- disjointAlist xs ((a,b):ys) =
--     (not $ any ((== a) . fst) xs) && disjointAlist xs ys

-- | Convert a maybe to a zero-or-one-element list.
asList :: Maybe a -> [a]
asList Nothing = []
asList (Just x) = [x]

isRight :: Either a b -> Bool
isRight (Right _) = True
isRight (Left _ ) = False

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft (Right _ ) = False

-- | zipAlist: given two alists with the same domain,
-- returns an alist mapping each of those domain values to
-- the pair of the two corresponding values from the given lists.
zipAlist xs ys = 
    let xsys = zip (sortAlist xs) (sortAlist ys) in
    if not $ and [x == y | ((x, a), (y, b)) <- xsys] then 
        error "alist mismatch in zipAlist"
    else [(x, (a, b)) | ((x, a), (y, b)) <- xsys]

-- | mapstrcat: transform a list to one of strings, with a given
-- | function, and join these together with some `glue' string.
mapstrcat :: String -> (a -> String) -> [a] -> String
mapstrcat glue f xs = concat $ List.intersperse glue (map f xs)

-- Functional utilities
eqUpTo f x y = f x == f y
