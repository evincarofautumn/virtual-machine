{-#
  LANGUAGE GADTs
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

pass :: (FuelMonad m) => BwdPass m Node LiveSet
pass = BwdPass
  { bp_lattice = lattice, bp_transfer = transfer, bp_rewrite = rewrite }

transfer :: BwdTransfer Node LiveSet
transfer = mkBTransfer3 analysisInitial analysisMedial analysisFinal

analysisInitial :: Node C O -> LiveSet -> LiveSet
analysisInitial NLabel{} facts = facts

-- A register is not alive before an assignment, so target registers are
-- always omitted from the fact base before proceeding.
analysisMedial :: Node O O -> LiveSet -> LiveSet
analysisMedial instruction facts = case instruction of
  NAdd out _ _ -> addUsesBut out
  NEquals out _ _ -> addUsesBut out
  NLessThan out _ _ -> addUsesBut out
  NMove out _ -> addUsesBut out
  NMultiply out _ _ -> addUsesBut out
  NNegate out _ -> addUsesBut out
  NNot out _ -> addUsesBut out
  NSet out _ -> addUsesBut out
  where addUsesBut x = addUses (Set.delete x facts) instruction

analysisFinal :: Node O C -> FactBase LiveSet -> LiveSet
analysisFinal instruction facts = case instruction of
  NJump label -> addUses (fact facts label) instruction
  NJumpIfZero _ true false
    -> addUses (fact facts true <> fact facts false) instruction
  NCall _ _ out label -> addUses (Set.delete out (fact facts label)) instruction
  NReturn _ -> addUses (fact_bot lattice) instruction

lattice :: DataflowLattice LiveSet
lattice = DataflowLattice
  { fact_name = "live registers"
  , fact_bot = Set.empty
  , fact_join = \_ (OldFact old) (NewFact new) -> let
    factChange = changeIf (Set.size factJoin > Set.size old)
    factJoin = old <> new
    in (factChange, factJoin)
  }

rewrite :: (FuelMonad m) => BwdRewrite m Node LiveSet
rewrite = mkBRewrite3 rewriteInitial rewriteMedial rewriteFinal

rewriteInitial :: (FuelMonad m) => n C O -> f -> m (Maybe (Graph n C O))
rewriteInitial _node _facts = return Nothing

rewriteMedial :: (FuelMonad m) => n O O -> f -> m (Maybe (Graph n O O))
rewriteMedial _node _facts = return Nothing

rewriteFinal :: (FuelMonad m) => n O C -> FactBase f -> m (Maybe (Graph n O C))
rewriteFinal _node _facts = return Nothing

fact :: FactBase (Set a) -> Label -> Set a
fact facts label = fromMaybe Set.empty $ lookupFact label facts

addUses :: LiveSet -> Node e x -> LiveSet
addUses to = (<> to) . registerSet
