module Optimize
  ( optimize
  ) where

import Compiler.Hoopl hiding ((<*>))

import Node
import Types

import qualified Optimize.ConstantFolding as ConstantFolding
import qualified Optimize.Liveness as Liveness

optimize
  :: Label
  -> Graph Node C C
  -> LabelMap Depth
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
