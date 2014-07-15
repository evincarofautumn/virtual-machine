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

-- | An instruction in the input program, indexed by whether it was constructed
-- by the optimizer. This avoids spurious cases when dealing with unoptimized
-- flat programs. There is some signature duplication, but it can't be factored
-- into type synonyms because those don't support strictness annotations.
data Instruction (a :: Origin) where
  IAddRR :: !Register -> !Register -> !Register -> Instruction a
  IAddRC :: !Register -> !Register -> !Constant -> Instruction Optimized
  IAddR :: !Register -> !Register -> Instruction Optimized
  IAddC :: !Register -> !Constant -> Instruction Optimized
  ICall
    :: {-lazy-}(Labelled Target)
    -> !Depth
    -> !Register
    -> {-lazy-}(Labelled Target)
    -> Instruction a
  IEqualsRR :: !Register -> !Register -> !Register -> Instruction a
  IEqualsRC :: !Register -> !Register -> !Constant -> Instruction Optimized
  IEqualsR :: !Register -> !Register -> Instruction Optimized
  IEqualsC :: !Register -> !Constant -> Instruction Optimized
  IJump :: {-lazy-}(Labelled Target) -> Instruction a
  IJumpIfZero
    :: !Register
    -> {-lazy-}(Labelled Target)
    -> {-lazy-}(Labelled Target)
    -> Instruction a
  ILessThanRR :: !Register -> !Register -> !Register -> Instruction a
  ILessThanRC :: !Register -> !Register -> !Constant -> Instruction Optimized
  ILessThanR :: !Register -> !Register -> Instruction Optimized
  ILessThanC :: !Register -> !Constant -> Instruction Optimized
  IMultiplyRR :: !Register -> !Register -> !Register -> Instruction a
  IMultiplyRC :: !Register -> !Register -> !Constant -> Instruction Optimized
  IMultiplyR :: !Register -> !Register -> Instruction Optimized
  IMultiplyC :: !Register -> !Constant -> Instruction Optimized
  INegateR :: !Register -> !Register -> Instruction a
  INegate :: !Register -> Instruction Optimized
  INotR :: !Register -> !Register -> Instruction a
  INot :: !Register -> Instruction Optimized
  IReturn :: !Register -> Instruction a
  ISetRR :: !Register -> !Register -> Instruction a
  ISetRC :: !Register -> !Constant -> Instruction a

deriving instance Show (Instruction a)

-- | A flat program of labelled instructions.
newtype FlatProgram a = FlatProgram
  { flatInstructions :: Vector (Labelled (Instruction a)) }
  deriving (Show)

-- | The origin of an instruction: parsing or optimization.
data Origin = Parsed | Optimized

-- | The set of labels to which an instruction may branch.
successorSet :: Instruction a -> Set Label
successorSet = \case
  ICall (Labelled l _) _ _ (Labelled n _) -> Set.fromList [l, n]
  IJump (Labelled l _) -> Set.singleton l
  IJumpIfZero _ (Labelled t _) (Labelled f _) -> Set.fromList [t, f]
  IReturn{} -> Set.empty
  _ -> Set.empty
