/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Graphs.Drawings.Grid.FinalFanQueryRankKeyOrder
import LeanTrominoes.Tiling.Polyomino.KeyedAlignedDatumRange
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Grouped.PeriodicCNFStripDirectSourceFinalGroupedOccurrenceIndexSemantics
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Fan.PeriodicCNFStripDirectSourceFinalFanRankLookup

/-! # Exact horizontal source order of compiled grouped occurrence indices -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

attribute [local instance]
  sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- The key lookup recovers exact variable-major occurrence order for the
compiled atom identity column. -/
theorem directSourceFinalGroupedOccurrenceIndices_eq_groupedIndices
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedOccurrenceIndices decider symbols =
      StableOccurrenceRanks.groupedIndices
        (directSourceFinalAtomIdentityCodes decider symbols) := by
  rw [directSourceFinalGroupedOccurrenceIndices_eq_map_alignedDatum]
  have lookup :
      (directSourceFinalUniqueFanQueryKeys decider symbols).map
        (UnaryKeyedValueLookup.alignedDatum
          (directSourceFinalOccurrenceCandidateKeys decider symbols)
          (directSourceFinalOccurrenceCandidateIndices decider symbols)) =
      (directSourceFinalUniqueFanQueryKeys decider symbols).map
        (fun key => (directSourceFinalOccurrenceCandidateKeys decider symbols).idxOf key) := by
    apply List.map_congr_left
    intro key member
    unfold directSourceFinalOccurrenceCandidateIndices UnaryFieldRange.values
    exact UnaryKeyedValueLookup.alignedDatum_range _ _
      (directSourceFinalUniqueFanQueryKey_mem_candidateKeys decider symbols key member)
  rw [lookup, directSourceFinalUniqueFanQueryKeys_eq,
    directSourceFinalOccurrenceCandidateKeys_eq_candidateKeys]
  exact FinalFanQueryRanks.dedup_keyedBlocks_map_idxOf _
    (fun value _member => directSourceFinalAtomIdentityCodes_count_le_three decider symbols value)

/-- Compiled regrouping uses the actual normalized source's exact variable
order and the actual incidence positions within each variable. -/
theorem directSourceFinalGroupedOccurrenceIndices_eq_horizontal
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedOccurrenceIndices decider symbols =
      StableOccurrenceRanks.groupedIndices
        (horizontalSemanticNormalizedRibbonSource
          (PeriodicCNF.ProgramSource.formulaOfSymbols decider symbols)).erase.variableOccurrences := by
  rw [directSourceFinalGroupedOccurrenceIndices_eq_groupedIndices,
    horizontalSemanticNormalizedRibbonSource_variableOccurrences]
  have identified := StableOccurrenceRanks.groupedIndices_eq_of_partition
    (directSourceFinalAtomIdentityCodes decider symbols)
    (horizontalRoutedFormulaComputed
      (PeriodicCNF.ProgramSource.formulaOfSymbols decider symbols)).erase.variableOccurrences
    (directSourceFinalAtomIdentityCodes_length_eq_horizontalAtoms decider symbols)
    (directSourceFinalAtomIdentityCodes_partition_horizontal decider symbols)
  simpa only [StableOccurrenceRanks.groupedIndices, List.idxsOf,
    Bool.beq_eq_decide_eq] using identified

end LeanTrominoes.PeriodicCNFStripReduction

end
