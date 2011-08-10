module Database.Narc.Rewrite where

import Data.Maybe (fromMaybe)

import Database.Narc.AST
import Database.Narc.Type
import Database.Narc.Util (alistmap)

-- | In @perhaps f x@, use @f@ to transform @x@, unless it declines by
-- returning @Nothing@, in which case return @x@ unchanged.
perhaps :: (a -> Maybe a) -> a -> a
perhaps f x = fromMaybe x (f x)

-- | Apply @f@ to each subterm of a given term, in a bottom-up fashion.
bu :: (Term a -> Maybe (Term a)) -> Term a -> Term a
bu f (Unit, d) = perhaps f (Unit, d)
bu f (Bool b, d) = perhaps f (Bool b, d)
bu f (Num n, d) = perhaps f (Num n, d)
bu f (Var x, d) = perhaps f (Var x, d)
bu f (Abs x n, d) = perhaps f (Abs x (bu f n), d)
bu f (App l m, d) = perhaps f (App (bu f l) (bu f m), d)
bu f (If c a b, d) =
    perhaps f (If (bu f c)
          (bu f a)
          (bu f b), d)
bu f (Table tab fields, d) = perhaps f (Table tab fields, d)
bu f (Singleton m, d) = perhaps f (Singleton (bu f m), d)
bu f (Record fields, d) = perhaps f (Record (alistmap (bu f) fields), d)
bu f (Project m a, d) = perhaps f (Project (bu f m) a, d)
bu f (Comp x src body, d) = perhaps f (Comp x (bu f src) (bu f body), d)
bu f (PrimApp fun args, d) = perhaps f (PrimApp fun args, d)
bu f (Nil, d) = perhaps f (Nil, d)
bu f (Union a b, d) = perhaps f (Union a b, d)

-- | Small-step version of compilation: local rewrite rules applied
-- willy-nilly. (Incomplete?)
rw (Comp x (Singleton m, _) n, t) = Just (substTerm x m n)
rw (App (Abs x n, st) m, t) = Just (substTerm x m n)
rw (Project (Record fields, rect) fld, t) = lookup fld fields
rw (Singleton (Var x, xT), t) = Nothing -- for now
rw (Comp x (Nil, _) n, t) = Just (Nil, t)
rw (Comp x m (Nil, _), t) = Just (Nil, t)
rw (Comp x (Comp y l m, s) n, t) = 
    if y `notElem` fvs n then
        Just (Comp y l (Comp x m n, t), t)
    else Nothing
rw (Comp x (m1 `Union` m2, s) n, t) =
    Just ((Comp x m1 n, t) `Union` (Comp x m2 n, t), t)
rw (Comp x m (n1 `Union` n2, _), t) =
    Just ((Comp x m n1, t) `Union` (Comp x m n2, t), t)
rw (Comp x (If b m (Nil, _), _) n, t) =
    Just (Comp x m (If b n (Nil, t), t), t)
rw (If (b, bTy) m n, t@(TList _, _)) | fst n /= Nil =
                      Just((If (b,bTy) m (Nil, t), t) `Union`
                           (If (PrimApp "not" [(b, bTy)], bTy) n (Nil, t), t), t)
rw (If b (Nil, _) (Nil, _), t) = Just (Nil, t)
rw (If b (Comp x m n, _) (Nil, _), t) = Just (Comp x m (If b n (Nil, t), t), t) 
rw (If b (m1 `Union` m2, _) (Nil, _), t) =
    Just ((If b m1 (Nil, t), t) `Union` (If b m2 (Nil, t), t), t)
-- push App inside If
-- push Project inside If
-- push If inside Record
-- rw (IsEmpty m, t) 
--     | lorob t   = Nothing
--     | otherwise = 
--         IsEmpty (Comp "x" m (Singleton (Unit, TUnit), TList Tunit), TList TUnit)
rw _ = Nothing
