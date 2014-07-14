{-# LANGUAGE GADTs, LambdaCase #-}

module Node
  ( Node(..)
  , registerSet
  ) where

import Compiler.Hoopl hiding ((<*>))
import Data.Set (Set)

import qualified Data.Set as Set

import Types

-- | An instruction in the intermediate representation, indexed by openness at
-- entry and exit: an instruction with a closed entry cannot be preceded by
-- another instruction, and an instruction with a closed exit cannot itself
-- precede another instruction. A basic block comprises a list of instructions,
-- closed at both ends.
data Node e x where
  NLabel :: Label -> Node C O
  NAdd :: Register -> Register -> Register -> Node O O
  NCall :: Label -> Depth -> Register -> Label -> Node O C
  NEquals :: Register -> Register -> Register -> Node O O
  NJump :: Label -> Node O C
  NJumpIfZero :: Register -> Label -> Label -> Node O C
  NLessThan :: Register -> Register -> Register -> Node O O
  NMove :: Register -> Register -> Node O O
  NMultiply :: Register -> Register -> Register -> Node O O
  NNegate :: Register -> Register -> Node O O
  NNot :: Register -> Register -> Node O O
  NReturn :: Register -> Node O C
  NSet :: Register -> Constant -> Node O O

instance Show (Node e x) where
  show = \case
    NLabel label -> show label ++ ":"
    NAdd a b c -> '\t' : unwords [show a, ":=", show b, "+", show c]
    NCall a _ b next -> '\t' : unwords [show b, ":= call", show a, "then", show next]
    NEquals a b c -> '\t' : unwords [show a, ":=", show b, "=", show c]
    NJump label -> '\t' : unwords ["jump", show label]
    NJumpIfZero a t f -> '\t' : unwords ["if", show a, "= 0 then", show t, "else", show f]
    NLessThan a b c -> '\t' : unwords [show a, ":=", show b, "<", show c]
    NMove a b -> '\t' : unwords [show a, ":=", show b]
    NMultiply a b c -> '\t' : unwords [show a, ":=", show b, "*", show c]
    NNegate a b -> '\t' : unwords [show a, ":= -", show b]
    NNot a b -> '\t' : unwords [show a, ":= not", show b]
    NReturn a -> '\t' : unwords ["ret", show a]
    NSet a b -> '\t' : unwords [show a, ":=", show b]

instance NonLocal Node where
  entryLabel (NLabel l) = l
  successors = \case
    NCall l _ _ n -> [l, n]
    NJump l -> [l]
    NJumpIfZero _ t f -> [t, f]
    NReturn{} -> []

registerSet :: Node e x -> Set Register
registerSet = \case
  NLabel{} -> Set.empty
  NAdd a b c -> Set.fromList [a, b, c]
  NCall _ _ a _ -> Set.singleton a
  NEquals a b c -> Set.fromList [a, b, c]
  NJump _ -> Set.empty
  NJumpIfZero a _ _ -> Set.singleton a
  NLessThan a b c -> Set.fromList [a, b, c]
  NMove a b -> Set.fromList [a, b]
  NMultiply a b c -> Set.fromList [a, b, c]
  NNegate a b -> Set.fromList [a, b]
  NNot a b -> Set.fromList [a, b]
  NReturn a -> Set.singleton a
  NSet a _ -> Set.singleton a