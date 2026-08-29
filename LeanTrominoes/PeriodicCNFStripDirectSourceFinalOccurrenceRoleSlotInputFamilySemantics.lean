/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFallbackQuerySlotBlockFamilyLength
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceRoleSlotInputBlockSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalStableRankSlotBlockFamilySemantics

/-! # Five-family semantics of final copied-clause slot inputs -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalSlotInputFamilyStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalSlotInputFamilyVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The compiled query/slot inputs split into the direct crossover prefix,
one combined carrier/bend fallback block, the direct routed-clause block,
and the direct routed-variable suffix. -/
theorem directSourceFinalClauseRouteTailRecordSlotInputs_eq_families
    (symbols : List encoding.Γ) :
    directSourceFinalClauseRouteTailRecordSlotInputs decider symbols =
      List.zip
          (directRetainedFinalCrossoverClauseQueries decider symbols)
          ((directSourceFinalCrossoverStableRankSlotBlocks
            decider symbols).map
              RetainedDirectClauseOccurrenceSlots.ofList) ++
        List.zip
          (directRetainedFinalCarrierClauseQueries decider symbols ++
            directRetainedFinalBendClauseQueries decider symbols)
          ((directSourceFinalCarrierStableRankSlotBlocks decider symbols ++
            directSourceFinalBendStableRankSlotBlocks decider symbols).map
              RetainedDirectClauseOccurrenceSlots.ofList) ++
          List.zip
            (directRetainedFinalRoutedClauseQueries decider symbols)
            ((directSourceFinalRoutedClauseStableRankSlotBlocks
              decider symbols).map
                RetainedDirectClauseOccurrenceSlots.ofList) ++
            List.zip
              (directRetainedFinalRoutedVariableClauseQueries
                decider symbols)
              ((directSourceFinalRoutedVariableStableRankSlotBlocks
                decider symbols).map
                  RetainedDirectClauseOccurrenceSlots.ofList) := by
  have crossoverLength :
      (directRetainedFinalCrossoverClauseQueries decider symbols).length =
        ((directSourceFinalCrossoverStableRankSlotBlocks
          decider symbols).map
            RetainedDirectClauseOccurrenceSlots.ofList).length := by
    simp only [List.length_map]
    exact (directRetainedFinalCrossoverClauseQueries_length
      decider symbols).trans
      (directSourceFinalCrossoverStableRankSlotBlocks_length
        decider symbols).symm
  have fallbackLength :
      (directRetainedFinalCarrierClauseQueries decider symbols ++
        directRetainedFinalBendClauseQueries decider symbols).length =
        ((directSourceFinalCarrierStableRankSlotBlocks
            decider symbols).map
              RetainedDirectClauseOccurrenceSlots.ofList ++
          (directSourceFinalBendStableRankSlotBlocks
            decider symbols).map
              RetainedDirectClauseOccurrenceSlots.ofList).length := by
    simpa only [List.length_append, List.length_map] using
      directSourceFinalFallbackQuerySlotBlocks_length decider symbols
  have routedClauseLength :
      (directRetainedFinalRoutedClauseQueries decider symbols).length =
        ((directSourceFinalRoutedClauseStableRankSlotBlocks
          decider symbols).map
            RetainedDirectClauseOccurrenceSlots.ofList).length := by
    simp only [List.length_map]
    exact (directRetainedFinalRoutedClauseQueries_length
      decider symbols).trans
      (directSourceFinalRoutedClauseStableRankSlotBlocks_length
        decider symbols).symm
  rw [directSourceFinalClauseRouteTailRecordSlotInputs_eq_zip_blocks]
  rw [directSourceFinalStableRankSlotBlocks_eq_fiveFamilies]
  unfold directRetainedFinalClauseQueryAssembly
    directRetainedFinalCarrierClauseQuerySuffix
    directRetainedFinalBendClauseQuerySuffix
    directRetainedFinalRoutedClauseQuerySuffix
  simp only [List.map_append, List.append_assoc]
  rw [List.zip_append crossoverLength]
  rw [← List.append_assoc
    (directRetainedFinalCarrierClauseQueries decider symbols)
    (directRetainedFinalBendClauseQueries decider symbols)
    (directRetainedFinalRoutedClauseQueries decider symbols ++
      directRetainedFinalRoutedVariableClauseQueries decider symbols)]
  rw [← List.append_assoc
    ((directSourceFinalCarrierStableRankSlotBlocks decider symbols).map
      RetainedDirectClauseOccurrenceSlots.ofList)
    ((directSourceFinalBendStableRankSlotBlocks decider symbols).map
      RetainedDirectClauseOccurrenceSlots.ofList)
    (((directSourceFinalRoutedClauseStableRankSlotBlocks
        decider symbols).map
          RetainedDirectClauseOccurrenceSlots.ofList) ++
      ((directSourceFinalRoutedVariableStableRankSlotBlocks
        decider symbols).map
          RetainedDirectClauseOccurrenceSlots.ofList))]
  rw [List.zip_append fallbackLength]
  rw [List.zip_append routedClauseLength]

end LeanTrominoes.PeriodicCNFStripReduction

end
