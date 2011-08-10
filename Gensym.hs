-- A Notion of Computation (Functor/Applicative/Monad) with a single
-- effect: fresh-name generation.

module Gensym (
    Gensym(..), gensym, runGensym
  ) where

import Control.Applicative

-- | The @Gensym@ computation type.

data Gensym a = G (Int -> (Int, a))

instance Monad Gensym where
    return v = G(\x -> (x,v))
    m >>= k = G(\x -> let G f = m in
                      let (x', v) = f x in 
                      let G f' = k v in f' x')

instance Functor Gensym where
    fmap f x = x >>= (return . f)

instance Applicative Gensym where
    pure = return
    f <*> x = do f' <- f ; x' <- x ; return (f' x')

-- | The effect for the @Gensym@ notion: generate a number which is
-- not returned again throughout the computation.
gensym :: Gensym Int
gensym = G(\x -> (x+1, x))

-- | Generate a fresh name, as a string, by prefixing it with the
-- given prefix. A wrapper aroung @gensym@ for convenience.
gensymStr :: String -> Gensym String
gensymStr prefix = do i <- gensym
                      return (prefix ++ (show i))

-- | Run the computation, generating fresh names, and extract the
-- result.
runGensym :: Gensym a -> a
runGensym (G f) = snd $ f 0

-- | This show instance allows you to return @Gensym@ computations in
-- | the interactive shell and display the results without worrying
-- | about the @Gensym@ wrapper.
instance Show a => Show (Gensym a) where
    show x = show $ runGensym x
