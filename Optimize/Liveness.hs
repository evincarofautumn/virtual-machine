{-#
  LANGUAGE GADTs
  , ScopedTypeVariables
  #-}

module Optimize.Liveness
  ( pass
  ) where

import Compiler.Hoopl hiding ((<*>))
import Data.Maybe
import Data.Monoid
import Data.Set (Set)

import qualified Data.Set as Set

import Node
import Types

type LiveSet = Set Register

-- | Performs liveness analysis and eliminates dead assignments.
pass :: (FuelMonad m) => LabelMap Depth -> BwdPass m Node LiveSet
pass depths = BwdPass
  { bp_lattice = lattice, bp_transfer = transfer depths, bp_rewrite = rewrite }

lattice :: DataflowLattice LiveSet
lattice = DataflowLattice
  { fact_name = "live registers"
  , fact_bot = Set.empty
  , fact_join = \_ (OldFact old) (NewFact new) -> let
    factChange = changeIf (Set.size factJoin > Set.size old)
    factJoin = old <> new
    in (factChange, factJoin)
  }

transfer :: LabelMap Depth -> BwdTransfer Node LiveSet
transfer depths = mkBTransfer3 initial medial final
  where
  initial :: Node C O -> LiveSet -> LiveSet
  initial NLabel{} facts = facts

  -- A register is not alive before an assignment, so destination registers are
  -- always omitted from the fact base before proceeding.
  medial :: Node O O -> LiveSet -> LiveSet
  medial instruction facts = case instruction of
    NAdd out _ _ -> addUsesBut out
    NEquals out _ _ -> addUsesBut out
    NLessThan out _ _ -> addUsesBut out
    NMultiply out _ _ -> addUsesBut out
    NNegate out _ -> addUsesBut out
    NNot out _ -> addUsesBut out
    NSet out _ -> addUsesBut out
    where addUsesBut x = addUses (Set.delete x facts) instruction

  final :: Node O C -> FactBase LiveSet -> LiveSet
  final instruction facts = case instruction of
    NJump label -> addUses (facts `about` label) instruction
    NJumpIfZero _ true false
      -> addUses ((facts `about` true) <> (facts `about` false)) instruction
    NCall target (Depth depth) out label
      -> addUses (arguments <> Set.delete out (facts `about` label)) instruction
      where
      arguments = Set.fromList $ map Register [maxArgument .. pred depth]
      maxArgument = case mapLookup target depths of
        Just (Depth known) -> depth - known
        -- We don't know which arguments the called procedure will use, so we
        -- conservatively assume it can use any of them, and that they are all
        -- therefore live at the point of the call. (This should not happen.)
        Nothing -> 0
    NReturn _ -> addUses (fact_bot lattice) instruction

rewrite :: forall m. (FuelMonad m) => BwdRewrite m Node LiveSet
rewrite = mkBRewrite3 initial medial final
  where
  initial :: Node C O -> LiveSet -> m (Maybe (Graph Node C O))
  initial _node _facts = return Nothing

  medial :: Node O O -> LiveSet -> m (Maybe (Graph Node O O))
  medial instruction facts = return $ case instruction of
    NAdd out _ _ | dead out -> Just emptyGraph
    NEquals out _ _ | dead out -> Just emptyGraph
    NLessThan out _ _ | dead out -> Just emptyGraph
    NMultiply out _ _ | dead out -> Just emptyGraph
    NNegate out _ | dead out -> Just emptyGraph
    NNot out _ | dead out -> Just emptyGraph
    NSet out _ | dead out -> Just emptyGraph
    _ -> Nothing
    where dead = (`Set.notMember` facts)

  final :: Node O C -> FactBase LiveSet -> m (Maybe (Graph Node O C))
  final _node _facts = return Nothing

about :: FactBase (Set a) -> Label -> Set a
facts `about` label = fromMaybe Set.empty $ lookupFact label facts

addUses :: LiveSet -> Node e x -> LiveSet
addUses to = (<> to) . registerSet
