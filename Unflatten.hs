{-# LANGUAGE ViewPatterns #-}

module Unflatten
  ( unflatten
  ) where

import Compiler.Hoopl hiding ((<*>))
import Data.List

import qualified Compiler.Hoopl as Hoopl
import qualified Data.Set as Set
import qualified Data.Vector as Vector

import Instruction
import Node
import Types
import Utils

-- | Unflattens a sequence of instructions into a control flow graph plus a
-- label indicating the entry point.
unflatten :: FlatProgram -> (Graph Node C C, Label)
unflatten (FlatProgram (Vector.toList -> instructions)) =
  ( foldl' (|*><*|) emptyClosedGraph blockified
  , labelledLabel $ head instructions
  )
  where
  blockified = map (uncurry blockify)
    . zip grouped
    $ map (Just . labelledLabel . head) (tail grouped) ++ [Nothing]

  usedLabels = mconcatMap (successorSet . labelledValue) instructions

  grouped = splitWhen
    (\x y -> isFinal x || labelledLabel y `Set.member` usedLabels)
    instructions

  blockify is@(i : _) mNext = let
    (medials, is') = spanJust toMedial is
    (mFinal, is'') = spanJust1 toFinal is'
    initial = NLabel $ labelledLabel i
    final = case (mFinal, is'') of
      (Just explicit, []) -> explicit
      (Nothing, []) -> case mNext of
        Just next -> NJump next
        Nothing -> error "Missing final instruction in final basic block."
      _ -> error "Multiple final instructions in basic block."
    in mkFirst initial Hoopl.<*> mkMiddles medials Hoopl.<*> mkLast final
  blockify [] _ = emptyClosedGraph

  toMedial (Labelled _ instruction) = case instruction of
    IAdd out left right -> Just $ NAdd out left right
    IEquals out left right -> Just $ NEquals out left right
    ILessThan out left right -> Just $ NLessThan out left right
    IMove out in_ -> Just $ NMove out in_
    IMultiply out left right -> Just $ NMultiply out left right
    INegate out in_ -> Just $ NNegate out in_
    INot out in_ -> Just $ NNot out in_
    ISet register constant -> Just $ NSet register constant
    _ -> Nothing

  toFinal (Labelled _ instruction) = case instruction of
    ICall (Labelled target _) depth register (Labelled next _)
      -> Just $ NCall target depth register next
    IJump (Labelled target _) -> Just $ NJump target
    IJumpIfZero register (Labelled target _) (Labelled next _)
      -> Just $ NJumpIfZero register target next
    IReturn register -> Just $ NReturn register
    _ -> Nothing

  isFinal (Labelled _ instruction) = case instruction of
    ICall{} -> True
    IJump{} -> True
    IJumpIfZero{} -> True
    IReturn{} -> True
    _ -> False
