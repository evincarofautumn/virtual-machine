{-#
  LANGUAGE DataKinds
  , GADTs
  , ViewPatterns
  #-}

module Unflatten
  ( unflatten
  ) where

import Compiler.Hoopl hiding ((<*>))
import Data.List
import Data.Maybe
import Data.Set (Set)

import qualified Compiler.Hoopl as Hoopl
import qualified Data.Set as Set
import qualified Data.Vector as Vector

import Instruction
import Node
import Types
import Utils

-- | Unflattens a sequence of instructions into a control flow graph plus a
-- label indicating the entry point.
unflatten :: FlatProgram Parsed -> (Graph Node C C, Label, LabelMap Depth)
unflatten (FlatProgram (Vector.toList -> instructions)) =
  ( foldl' (|*><*|) emptyClosedGraph blockified
  , labelledLabel $ head instructions
  , mapFromList $ mapMaybe
    (\block -> fmap
      ((,) (head . setElems $ labelsDefined block)
        . (\ (Register n) -> Depth (abs n)))
      $ foldGraphNodes
        (min . minRegisterMaybe)
        block
        (Just (Register 0)))
    blockified
  )
  where
  blockified :: [Graph Node C C]
  blockified = zipWith blockify grouped
    $ map (Just . labelledLabel . head) (tail grouped) ++ [Nothing]

  usedLabels :: Set Label
  usedLabels = mconcatMap (successorSet . labelledValue) instructions

  grouped :: [[Labelled (Instruction Parsed)]]
  grouped = splitWhen
    (\x y -> isFinal x || labelledLabel y `Set.member` usedLabels)
    instructions

  blockify :: [Labelled (Instruction a)] -> Maybe Label -> Graph Node C C
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

  toMedial :: Labelled (Instruction a) -> Maybe (Node O O)
  toMedial (Labelled _ instruction) = case instruction of
    IAddRR out left right -> Just $ NAdd out left (Dynamic right)
    IEqualsRR out left right -> Just $ NEquals out left (Dynamic right)
    ILessThanRR out left right -> Just $ NLessThan out left (Dynamic right)
    IMultiplyRR out left right -> Just $ NMultiply out left (Dynamic right)
    INegateR out in_ -> Just $ NNegate out in_
    INotR out in_ -> Just $ NNot out in_
    ISetRR out in_ -> Just $ NSet out (Dynamic in_)
    ISetRC register constant -> Just $ NSet register (Static constant)
    _ -> Nothing

  toFinal :: Labelled (Instruction a) -> Maybe (Node O C)
  toFinal (Labelled _ instruction) = case instruction of
    ICall (Labelled target _) depth register (Labelled next _)
      -> Just $ NCall target depth register next
    IJump (Labelled target _) -> Just $ NJump target
    IJumpIfZero register (Labelled target _) (Labelled next _)
      -> Just $ NJumpIfZero register target next
    IReturn register -> Just $ NReturn register
    _ -> Nothing

  isFinal :: Labelled (Instruction a) -> Bool
  isFinal (Labelled _ instruction) = case instruction of
    ICall{} -> True
    IJump{} -> True
    IJumpIfZero{} -> True
    IReturn{} -> True
    _ -> False

-- | The minimum register used by a node, if any.
minRegisterMaybe :: Node e x -> Maybe Register
minRegisterMaybe node = let
  set = registerSet node
  in if Set.null set then Nothing else Just (Set.findMin set)
