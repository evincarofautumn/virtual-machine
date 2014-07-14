module Optimize
  ( optimize
  ) where

import Compiler.Hoopl hiding ((<*>))

import Node

import qualified Optimize.Liveness as Liveness

optimize
  :: Label
  -> Graph Node C C
  -> SimpleUniqueMonad (Graph Node C C)
optimize entry program = runWithFuel infiniteFuel rewrite
  where
  rewrite :: SimpleFuelMonad (Graph Node C C)
  rewrite = do
    (rewritten, _, _) <- analyzeAndRewriteBwd
      Liveness.pass
      (JustC entry)
      program
      noFacts
    return rewritten
