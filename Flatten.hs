{-#
  LANGUAGE DataKinds
  , GADTs
  #-}

module Flatten
  ( flatten
  ) where

import Compiler.Hoopl hiding ((<*>))
import Data.Map (Map)
import Data.Maybe
import Data.Vector (Vector)

import qualified Data.Map as Map
import qualified Data.Vector as Vector

import Instruction
import Node
import Types
import Utils

-- | Flattens a control flow graph into executable instructions, selecting basic
-- or 'Optimized' instructions as appropriate. Returns the program and the
-- 'Target' address of the entry point.
flatten :: Label -> Graph Node C C -> (Target, Vector (Instruction Optimized))
flatten entry graph =
  ( labelledValue $ targetForLabel entry
  , Vector.reverse $ Vector.fromList finalInstructions
  )
  where
  finalLabels :: Map Label Int
  finalInstructions :: [Instruction Optimized]
  (finalLabels, finalInstructions)
    = foldGraphNodes addNode graph (Map.empty, [])

  targetForLabel :: Label -> Labelled Target
  targetForLabel label = Labelled label . Target
    . fromMaybe (error $ unwords ["Missing target for label", show label])
    $ Map.lookup label finalLabels

  addNode :: Node e x -> Build (Map Label Int, [Instruction Optimized])
  addNode i (labels, is) = case i of
    NLabel label -> (Map.insert label (length is) labels, is)
    NAdd out left right -> instruction $ if out == left
      then operand (IAddR out) (IAddC out) right
      else operand (IAddRR out left) (IAddRC out left) right
    NCall target depth out next -> instruction
      $ ICall (targetForLabel target) depth out (targetForLabel next)
    NEquals out left right -> instruction $ if out == left
      then operand (IEqualsR out) (IEqualsC out) right
      else operand (IEqualsRR out left) (IEqualsRC out left) right
    NJump target -> instruction $ IJump (targetForLabel target)
    NJumpIfZero register true false -> instruction
      $ IJumpIfZero register (targetForLabel true) (targetForLabel false)
    NLessThan out left right -> instruction $ if out == left
      then operand (ILessThanR out) (ILessThanC out) right
      else operand (ILessThanRR out left) (ILessThanRC out left) right
    NMultiply out left right -> instruction $ if out == left
      then operand (IMultiplyR out) (IMultiplyC out) right
      else operand (IMultiplyRR out left) (IMultiplyRC out left) right
    NNegate out in_ -> instruction
      $ if out == in_ then INegate out else INegateR out in_
    NNot out in_ -> instruction
      $ if out == in_ then INot out else INotR out in_
    NReturn register -> instruction $ IReturn register
    NSet out in_ -> instruction $ operand (ISetRR out) (ISetRC out) in_
    where instruction x = (labels, x : is)
