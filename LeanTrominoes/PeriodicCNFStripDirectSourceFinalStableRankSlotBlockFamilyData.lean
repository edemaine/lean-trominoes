/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFamilyStarts
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalStableRankSlotBlockData

/-! # Five-family direct-source stable-rank slot-block data -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalSlotBlockFamilyDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalSlotBlockFamilyDataVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Stable-rank slot blocks for an explicitly indexed final clause family. -/
def directSourceFinalStableRankSlotBlocksFrom
    (symbols : List encoding.Γ)
    (start : Nat)
    (clauses : List
      (PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))) :
    List (List RetainedTerminalSlot) :=
  let formula := directSourceFormula decider symbols
  (clauses.zipIdx start).map
    (retainedOccurrenceGlobalStableTerminalSlotBlock
      (retainedFinalCoordinatedScaledSource formula).erase
      (retainedFinalCoordinatedScaledSourceRoutes formula))

@[simp] theorem directSourceFinalStableRankSlotBlocksFrom_length
    (symbols : List encoding.Γ)
    (start : Nat)
    (clauses : List
      (PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))) :
    (directSourceFinalStableRankSlotBlocksFrom
      decider symbols start clauses).length = clauses.length := by
  unfold directSourceFinalStableRankSlotBlocksFrom
  simp only [List.length_map, List.length_zipIdx]

def directSourceFinalCrossoverStableRankSlotBlocks
    (symbols : List encoding.Γ) :=
  directSourceFinalStableRankSlotBlocksFrom decider symbols 0
    (directSourceFinalCrossoverClauses decider symbols)

def directSourceFinalCarrierStableRankSlotBlocks
    (symbols : List encoding.Γ) :=
  directSourceFinalStableRankSlotBlocksFrom decider symbols
    (directSourceFinalCarrierStart decider symbols)
    (directSourceFinalCarrierClauses decider symbols)

def directSourceFinalBendStableRankSlotBlocks
    (symbols : List encoding.Γ) :=
  directSourceFinalStableRankSlotBlocksFrom decider symbols
    (directSourceFinalBendStart decider symbols)
    (directSourceFinalBendClauses decider symbols)

def directSourceFinalRoutedClauseStableRankSlotBlocks
    (symbols : List encoding.Γ) :=
  directSourceFinalStableRankSlotBlocksFrom decider symbols
    (directSourceFinalRoutedClauseStart decider symbols)
    (directSourceFinalRoutedClauseClauses decider symbols)

def directSourceFinalRoutedVariableStableRankSlotBlocks
    (symbols : List encoding.Γ) :=
  directSourceFinalStableRankSlotBlocksFrom decider symbols
    (directSourceFinalRoutedVariableStart decider symbols)
    (directSourceFinalRoutedVariableClauses decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end
