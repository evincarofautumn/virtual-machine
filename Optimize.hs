module Optimize
  ( optimize
  ) where

import Compiler.Hoopl hiding ((<*>))

import Node
import Types

import qualified Optimize.ConstantFolding as ConstantFolding
import qualified Optimize.Liveness as Liveness

-- | Optimizes a control flow graph from the specified entry point.
optimize
  :: Label  -- ^ Entry point.
  -> Graph Node C C  -- ^ Control flow graph.
  -> LabelMap Depth  -- ^ Number of arguments used by each basic block.
  -> SimpleUniqueMonad (Graph Node C C)
optimize entry program depths = runWithFuel infiniteFuel rewrite
  where
  rewrite :: SimpleFuelMonad (Graph Node C C)
  rewrite = do
    (program', _, _) <- analyzeAndRewriteFwd
      ConstantFolding.pass (JustC [entry]) program
      (ConstantFolding.initialFacts entry)
    (program'', _, _) <- analyzeAndRewriteBwd
      (Liveness.pass depths) (JustC [entry]) program' noFacts
    return program''
