/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalStableRankSlotBlockFamilyData

/-! # Five-family semantics of direct-source stable-rank slot blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalSlotBlockFamilySemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalSlotBlockFamilySemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

theorem directSourceFinalStableRankSlotBlocksFrom_append
    (symbols : List encoding.Γ)
    (start : Nat)
    (first second : List
      (PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))) :
    directSourceFinalStableRankSlotBlocksFrom decider symbols start
        (first ++ second) =
      directSourceFinalStableRankSlotBlocksFrom decider symbols start first ++
        directSourceFinalStableRankSlotBlocksFrom decider symbols
          (start + first.length) second := by
  unfold directSourceFinalStableRankSlotBlocksFrom
  rw [List.zipIdx_append, List.map_append]

theorem directSourceFinalStableRankSlotBlocks_eq_from_deduplicated
    (symbols : List encoding.Γ) :
    directSourceFinalStableRankSlotBlocks decider symbols =
      directSourceFinalStableRankSlotBlocksFrom decider symbols 0
        (deduplicatedClauses (directSourceFormula decider symbols)) := by
  rw [directSourceFinalStableRankSlotBlocks_eq]
  unfold retainedOccurrenceGlobalStableTerminalSlotBlocks
    directSourceFinalStableRankSlotBlocksFrom
  rw [directSourceFinalScaledClauses_eq decider symbols]

/-- The global block stream splits in the same crossover, carrier, bend,
routed-clause, and routed-variable order as the final query assembly. -/
theorem directSourceFinalStableRankSlotBlocks_eq_fiveFamilies
    (symbols : List encoding.Γ) :
    directSourceFinalStableRankSlotBlocks decider symbols =
      (directSourceFinalCrossoverStableRankSlotBlocks decider symbols ++
        directSourceFinalCarrierStableRankSlotBlocks decider symbols) ++
      ((directSourceFinalBendStableRankSlotBlocks decider symbols ++
        directSourceFinalRoutedClauseStableRankSlotBlocks decider symbols) ++
        directSourceFinalRoutedVariableStableRankSlotBlocks
          decider symbols) := by
  rw [directSourceFinalStableRankSlotBlocks_eq_from_deduplicated]
  rw [directSource_deduplicatedClauses_eq_fiveFamilies]
  rw [directSourceFinalFiveFamilyClauses_eq_named]
  rw [directSourceFinalStableRankSlotBlocksFrom_append]
  rw [directSourceFinalStableRankSlotBlocksFrom_append]
  rw [directSourceFinalStableRankSlotBlocksFrom_append]
  rw [directSourceFinalStableRankSlotBlocksFrom_append]
  unfold directSourceFinalCrossoverStableRankSlotBlocks
    directSourceFinalCarrierStableRankSlotBlocks
    directSourceFinalBendStableRankSlotBlocks
    directSourceFinalRoutedClauseStableRankSlotBlocks
    directSourceFinalRoutedVariableStableRankSlotBlocks
  simp only [directSourceFinalRoutedVariableStart,
    directSourceFinalRoutedClauseStart, directSourceFinalBendStart,
    directSourceFinalCarrierStart, List.length_append, Nat.zero_add,
    Nat.add_assoc]

end LeanTrominoes.PeriodicCNFStripReduction

end
