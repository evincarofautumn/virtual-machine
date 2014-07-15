{-# LANGUAGE GADTs, LambdaCase #-}

module Node
  ( Node(..)
  , Operand(..)
  , operand
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
  NLabel :: !Label -> Node C O
  NAdd :: !Register -> !Register -> !Operand -> Node O O
  NCall :: !Label -> !Depth -> !Register -> !Label -> Node O C
  NEquals :: !Register -> !Register -> !Operand -> Node O O
  NJump :: !Label -> Node O C
  NJumpIfZero :: !Register -> !Label -> !Label -> Node O C
  NLessThan :: !Register -> !Register -> !Operand -> Node O O
  NMultiply :: !Register -> !Register -> !Operand -> Node O O
  NNegate :: !Register -> !Register -> Node O O
  NNot :: !Register -> !Register -> Node O O
  NReturn :: !Register -> Node O C
  NSet :: !Register -> !Operand -> Node O O

-- | An operand to an instruction.
data Operand
  = Dynamic !Register  -- ^ Register
  | Static !Constant  -- ^ Immediate
  deriving (Eq, Ord)

-- | Case analysis on operands.
operand :: (Register -> a) -> (Constant -> a) -> Operand -> a
operand dynamic _ (Dynamic x) = dynamic x
operand _ static (Static x) = static x

instance Show Operand where
  show (Dynamic register) = show register
  show (Static constant) = show constant

instance Show (Node e x) where
  show = \case
    NLabel label -> show label ++ ":"
    NAdd a b c -> '\t' : unwords [show a, ":=", show b, "+", show c]
    NCall a _ b next -> '\t' : unwords
      [show b, ":= call", show a, "then", show next]
    NEquals a b c -> '\t' : unwords [show a, ":=", show b, "=", show c]
    NJump label -> '\t' : unwords ["jump", show label]
    NJumpIfZero a t f -> '\t' : unwords
      ["if", show a, "= 0 then", show t, "else", show f]
    NLessThan a b c -> '\t' : unwords [show a, ":=", show b, "<", show c]
    NMultiply a b c -> '\t' : unwords [show a, ":=", show b, "*", show c]
    NNegate a b -> '\t' : unwords [show a, ":= -", show b]
    NNot a b -> '\t' : unwords [show a, ":= not", show b]
    NReturn a -> '\t' : unwords ["ret", show a]
    NSet a b -> '\t' : unwords [show a, ":=", show b]

-- | The set of labels to which a final instruction may branch.
instance NonLocal Node where
  entryLabel (NLabel l) = l
  successors = \case
    NCall l _ _ n -> [l, n]
    NJump l -> [l]
    NJumpIfZero _ t f -> [t, f]
    NReturn{} -> []

-- | The set of registers read or written by a node.
registerSet :: Node e x -> Set Register
registerSet = \case
  NLabel{} -> Set.empty
  NAdd a b c -> Set.fromList $ [a, b] ++ [r | Dynamic r <- [c]]
  NCall _ _ a _ -> Set.singleton a
  NEquals a b c -> Set.fromList $ [a, b] ++ [r | Dynamic r <- [c]]
  NJump _ -> Set.empty
  NJumpIfZero a _ _ -> Set.singleton a
  NLessThan a b c -> Set.fromList $ [a, b] ++ [r | Dynamic r <- [c]]
  NMultiply a b c -> Set.fromList $ [a, b] ++ [r | Dynamic r <- [c]]
  NNegate a b -> Set.fromList [a, b]
  NNot a b -> Set.fromList [a, b]
  NReturn a -> Set.singleton a
  NSet a b -> Set.fromList $ [a] ++ [r | Dynamic r <- [b]]
