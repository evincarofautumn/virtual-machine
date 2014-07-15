{-#
  LANGUAGE DataKinds
  , GADTs
  , KindSignatures
  , LambdaCase
  , StandaloneDeriving
  #-}

module Instruction
  ( FlatProgram(..)
  , Instruction(..)
  , Origin(..)
  , successorSet
  ) where

import Compiler.Hoopl hiding ((<*>))
import Data.Set (Set)
import Data.Vector (Vector)

import qualified Data.Set as Set

import Types

newtype FlatProgram a = FlatProgram
  { flatInstructions :: Vector (Labelled (Instruction a)) }
  deriving (Show)

data Origin = Parsed | Optimized

-- | An instruction in the input program, indexed by whether it was constructed
-- by the parser or by the optimizer.
data Instruction (a :: Origin) where
  IAddRR :: !Register -> !Register -> !Register -> Instruction a
  IAddRC :: !Register -> !Register -> !Constant -> Instruction a
  ICall :: {-lazy-}(Labelled Target) -> !Depth -> !Register -> {-lazy-}(Labelled Target) -> Instruction a
  IEqualsRR :: !Register -> !Register -> !Register -> Instruction a
  IEqualsRC :: !Register -> !Register -> !Constant -> Instruction a
  IJump :: {-lazy-}(Labelled Target) -> Instruction a
  IJumpIfZero :: !Register -> {-lazy-}(Labelled Target) -> {-lazy-}(Labelled Target) -> Instruction a
  ILessThanRR :: !Register -> !Register -> !Register -> Instruction a
  ILessThanRC :: !Register -> !Register -> !Constant -> Instruction a
  IMove :: !Register -> !Register -> Instruction a
  IMultiplyRR :: !Register -> !Register -> !Register -> Instruction a
  IMultiplyRC :: !Register -> !Register -> !Constant -> Instruction a
  INegate :: !Register -> !Register -> Instruction a
  INot :: !Register -> !Register -> Instruction a
  IReturn :: !Register -> Instruction a
  ISet :: !Register -> !Constant -> Instruction a

deriving instance Show (Instruction a)

successorSet :: Instruction a -> Set Label
successorSet = \case
  ICall (Labelled l _) _ _ (Labelled n _) -> Set.fromList [l, n]
  IJump (Labelled l _) -> Set.singleton l
  IJumpIfZero _ (Labelled t _) (Labelled f _) -> Set.fromList [t, f]
  IReturn{} -> Set.empty
  _ -> Set.empty
