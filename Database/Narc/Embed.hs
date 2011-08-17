{-# LANGUAGE TypeSynonymInstances, MultiParamTypeClasses #-}

module Database.Narc.Embed where

import Control.Applicative

import Algebras
import Gensym

import Database.Narc.Type
import Database.Narc.AST

-- HOAS-ish embedded language.

type NarcTerm = Gensym (Term ())

-- | Turn a HOAS representation of a Narc term into a concrete,
-- | named-binder representation.
realize :: NarcTerm -> Term ()
realize = runGensym

-- | A dummy value, or zero-width record.
unit :: NarcTerm
unit = return $ (!) Unit

-- | A polymorphic way of embedding constants into a term.
class Constable a where
    -- | Lift a constant value into a query.
    -- @Constable@ types currently include @Bool@ and @Integer@.
    cnst :: a -> NarcTerm
instance Constable Bool    where cnst b = return ((!)(Bool b))
instance Constable Integer where cnst n = return ((!)(Num n))
instance Constable String  where cnst s = return ((!)(String s))

-- | Apply some primitive function, such as @(+)@ or @avg@, to a list
-- of arguments.
primApp :: String -> [NarcTerm] -> NarcTerm
primApp f args =  (!) . PrimApp f <$> sequence args

-- | Create a functional abstraction.
abs :: (String -> NarcTerm) -> NarcTerm
abs fn = do
  n <- gensym
  let x = '_' : show n
  body <- fn x
  return $ (!) $ Abs x body

-- | Apply a functional term to an argument.
app :: NarcTerm -> NarcTerm -> NarcTerm
app l m = (!) <$> (App <$> l <*> m)

-- | A reference to a named database table; second argument is its
-- schema type.
table :: Tabname -> [(Field, Type)] -> NarcTerm
table tbl ty = return $ (!) $ Table tbl ty

-- | A condition between two terms, as determined by the boolean value
-- of the first term.
ifthenelse :: NarcTerm -> NarcTerm -> NarcTerm -> NarcTerm
ifthenelse c t f = (!) <$> (If <$> c <*> t <*> f)

-- | A singleton collection of one item.
singleton :: NarcTerm -> NarcTerm
singleton x = (!) . Singleton <$> x

-- | An empty collection.
nil :: NarcTerm
nil = return $ (!) $ Nil

-- | The union of two collections
union :: NarcTerm -> NarcTerm -> NarcTerm
union l r = (!) <$> (Union <$> l <*> r)

-- | Construct a record (name-value pairs) out of other terms; usually
-- used, with base values for the record elements, as the final
-- result of a query, corresponding to the @select@ clause of a SQL
-- query, but can also be used with nested results internally in a
-- query.
record :: [(String, NarcTerm)] -> NarcTerm
record fields = (!) <$> (Record <$> sequence [do expr' <- expr ; return (lbl, expr') | (lbl, expr) <- fields])

-- | Project a field out of a record value.
project :: NarcTerm -> String -> NarcTerm
project expr field = (!) <$> (Project <$> expr <*> return field)

-- | For each item in the collection resulting from the first
-- argument, give it to the function which is the second argument
-- and evaluate--this corresponds to a loop, or two one part of a
-- cross in traditional SQL queries.
foreach :: NarcTerm -> (NarcTerm -> NarcTerm) -> NarcTerm
foreach src k = do
  src' <- src
  n <- gensym
  let x = '_' : show n
  body' <- k (return (var_ x))
  return $ (!)(Comp x src' body')

-- | Filter the current iteration as per the condition in the first
-- argument. Corresponds to a @where@ clause in a SQL query.
having :: NarcTerm -> NarcTerm -> NarcTerm
having cond body = ifthenelse cond body nil

-- | A shortcut for giving the typical bottom of a ``FLWOR-style''
-- comprehension:
--
-- > foreach t $ \row ->
-- > having (project x "a" > 2) $ 
-- > result [("result", project x "b")]
result :: [(String, NarcTerm)] -> NarcTerm
result x = singleton $ record x
