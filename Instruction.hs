{-# LANGUAGE LambdaCase #-}

module Instruction
  ( FlatProgram(..)
  , Instruction(..)
  , successorSet
  ) where

import Compiler.Hoopl hiding ((<*>))
import Data.Set (Set)
import Data.Vector (Vector)

import qualified Data.Set as Set

import Types

newtype FlatProgram = FlatProgram
  { flatInstructions :: Vector (Labelled Instruction) }
  deriving (Show)

-- | An instruction in the input program.
data Instruction
  = IAdd !Register !Register !Register
  | ICall {-lazy-}(Labelled Target) !Depth !Register {-lazy-}(Labelled Target)
  | IEquals !Register !Register !Register
  | IJump {-lazy-}(Labelled Target)
  | IJumpIfZero !Register {-lazy-}(Labelled Target) {-lazy-}(Labelled Target)
  | ILessThan !Register !Register !Register
  | IMove !Register !Register
  | IMultiply !Register !Register !Register
  | INegate !Register !Register
  | INot !Register !Register
  | IReturn !Register
  | ISet !Register !Constant
  deriving (Show)

successorSet :: Instruction -> Set Label
successorSet = \case
  ICall (Labelled l _) _ _ (Labelled n _) -> Set.fromList [l, n]
  IJump (Labelled l _) -> Set.singleton l
  IJumpIfZero _ (Labelled t _) (Labelled f _) -> Set.fromList [t, f]
  IReturn{} -> Set.empty
  _ -> Set.empty
