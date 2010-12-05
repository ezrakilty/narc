module Gensym (
    Gensym(..), gensym, runGensym
  ) where

import Control.Applicative

-- Gensym monad

data Gensym a = G (Int -> (Int, a))

instance Monad Gensym where
    return v = G(\x -> (x,v))
    m >>= k = G(\x -> let G f = m in
                      let (x', v) = f x in 
                      let G f' = k v in f' x')

instance Functor Gensym where
    fmap f x = x >>= (return . f)

instance Control.Applicative.Applicative Gensym where
    pure = return
    f <*> x = do f' <- f ; x' <- x ; return (f' x')

gensym :: Gensym Int
gensym = G(\x -> (x+1, x))

runGensym (G f) = snd $ f 0

instance Show a => Show (Gensym a) where
    show x = show $ runGensym x
