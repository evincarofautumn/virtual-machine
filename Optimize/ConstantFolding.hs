{-#
  LANGUAGE GADTs
  , PatternGuards
  , ScopedTypeVariables
  #-}

module Optimize.ConstantFolding
  ( initialFacts
  , pass
  ) where

import Compiler.Hoopl hiding ((<*>))
import Data.Map (Map)

import qualified Data.Map as Map

import Node
import Types

type ValueSet = Map Register (WithTop Constant)

pass :: (FuelMonad m) => FwdPass m Node ValueSet
pass = FwdPass
  { fp_lattice = lattice, fp_transfer = transfer, fp_rewrite = rewrite }

lattice :: DataflowLattice ValueSet
lattice = DataflowLattice
  { fact_name = "constant registers"
  , fact_bot = Map.empty
  , fact_join = joinMaps . extendJoinDomain $ \_ (OldFact old) (NewFact new)
    -> if old == new then (NoChange, PElem new) else (SomeChange, Top)
  }

transfer :: FwdTransfer Node ValueSet
transfer = mkFTransfer3 initial medial final
  where
  initial :: Node C O -> ValueSet -> ValueSet
  initial NLabel{} facts = facts

  medial :: Node O O -> ValueSet -> ValueSet
  medial instruction facts = case instruction of
    NAdd out _ _ -> top out
    NEquals out a b
      -- x == x is always true.
      -> if Dynamic a == b
        then Map.insert out (PElem (Constant 1)) facts
        else top out
    NLessThan out a b
      -- x < x is always false.
      -> if Dynamic a == b
        then Map.insert out (PElem (Constant 0)) facts
        else top out
    NMove out a
      -- Self-assignment does not destroy information.
      -> if a == out then facts else top out
    NMultiply out _ _ -> top out
    NNegate out _ -> top out
    NNot out _ -> top out
    NSet out constant -> Map.insert out (PElem constant) facts
    where top x = Map.insert x Top facts

  final :: Node O C -> ValueSet -> FactBase ValueSet
  final instruction facts = case instruction of
    NJump label -> mapSingleton label facts
    NJumpIfZero condition true false
      -- If we took the branch, then we know the value of the register.
      -> mkFactBase lattice
        [ (true, Map.insert condition (PElem (Constant 1)) facts)
        , (false, Map.insert condition (PElem (Constant 0)) facts)
        ]
    NCall target (Depth _depth) out next
      -> mkFactBase lattice
        [ (target, facts)
        , (next, foldr (\v -> Map.insert v Top) facts (out : arguments))
        ]
      where
      -- We don't know which arguments the called procedure will overwrite, so
      -- we can conservatively assume it can overwrite any of them, and that
      -- they are all therefore non-constant after the call:
      --
      -- > arguments = map Register [0 .. pred depth]
      --
      -- But that's no fun.
      --
      arguments = []
    NReturn _ -> mapEmpty

rewrite :: forall m. (FuelMonad m) => FwdRewrite m Node ValueSet
rewrite = mkFRewrite3 initial medial final
  where
  initial :: Node C O -> ValueSet -> m (Maybe (Graph Node C O))
  initial _node _facts = return Nothing

  medial :: Node O O -> ValueSet -> m (Maybe (Graph Node O O))
  medial instruction facts = case instruction of
    NAdd out left (Dynamic right)
      -> match right $ NAdd out left . Static . Constant
    NAdd out left (Static (Constant right))
      -> match left $ NSet out . Constant . (+ right)
    NEquals out left (Dynamic right)
      -> match right $ NEquals out left . Static . Constant
    NEquals out left (Static (Constant right))
      -> match left $ NSet out . Constant . fromIntegral . fromEnum . (== right)
    NLessThan out left (Dynamic right)
      -> match right $ NLessThan out left . Static . Constant
    NLessThan out left (Static (Constant right))
      -> match left $ NSet out . Constant . fromIntegral . fromEnum . (< right)
    NMultiply out left (Dynamic right)
      -> match right $ NMultiply out left . Static . Constant
    NMultiply out left (Static (Constant right))
      -> match left $ NSet out . Constant . (* right)
    _ -> return Nothing
    where
    match :: Register -> (Cell -> Node O O) -> m (Maybe (Graph Node O O))
    match register f = case Map.lookup register facts of
      Just (PElem (Constant constant)) -> return . Just . mkMiddle $ f constant
      _ -> return Nothing

  final :: Node O C -> ValueSet -> m (Maybe (Graph Node O C))
  final _node _facts = return Nothing

initialFacts :: Label -> FactBase ValueSet
initialFacts entry
  = mapSingleton entry
  $ Map.fromList [(Register r, Top) | r <- [0 .. registerLimit]]

-- | An arbitrary limit on the number of registers that may be active at once.
registerLimit :: Int
registerLimit = 256
