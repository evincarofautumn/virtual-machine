module IdMap
  ( IdMap
  , IdMapMonad
  , labelForTarget
  , runIdMap
  ) where

import Compiler.Hoopl hiding ((<*>))
import Control.Applicative
import Data.IntMap (IntMap)

import qualified Data.IntMap as IntMap

import Types

type IdMap = IntMap Label

-- | A monad for generating fresh labels associated with IDs.
newtype IdMapMonad a = IdMapMonad
  { unIdMap :: IdMap -> SimpleUniqueMonad (IdMap, a) }

instance Monad IdMapMonad where
  return x = IdMapMonad $ \env -> return (env, x)
  IdMapMonad f >>= m = IdMapMonad $ \env -> do
    (env', x) <- f env
    unIdMap (m x) env'

instance Functor IdMapMonad where
  fmap f m = m >>= return . f

instance Applicative IdMapMonad where
  pure x = IdMapMonad $ \env -> return (env, x)
  mf <*> mx = do
    f <- mf
    x <- mx
    return $ f x

-- | Retrieves the label for a given target or creates a fresh one for it.
labelForTarget :: Target -> IdMapMonad Label
labelForTarget (Target index) = IdMapMonad
  $ \env -> case IntMap.lookup index env of
    Just existing -> return (env, existing)
    Nothing -> do
      label <- freshLabel
      return (IntMap.insert index label env, label)

-- | Runs an action with a fresh id-label mapping.
runIdMap :: IdMapMonad a -> SimpleUniqueMonad (IdMap, a)
runIdMap (IdMapMonad m) = m IntMap.empty
