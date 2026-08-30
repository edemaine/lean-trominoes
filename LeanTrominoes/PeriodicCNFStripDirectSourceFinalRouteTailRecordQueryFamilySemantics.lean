/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceRoleSlotInputFamilySemantics
import LeanTrominoes.RetainedAngularFanDirectClauseRouteTailRecordSlotAttachmentListSemantics

/-! # Direct-family semantics of final route-tail record queries -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalRouteTailFamilyStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Slot attachment rejects the two fallback families and preserves exactly
the crossover, routed-clause, and routed-variable query blocks. -/
theorem directSourceFinalClauseRouteTailRecordQueries_eq_directFamilies
    (symbols : List encoding.Γ) :
    retainedDirectClauseRouteTailRecordQueriesOfSlotInputs
        (directSourceFinalClauseRouteTailRecordSlotInputs decider symbols) =
      retainedDirectClauseRouteTailRecordQueriesOfSlotInputs
          (List.zip
            (directRetainedFinalCrossoverClauseQueries decider symbols)
            ((directSourceFinalCrossoverStableRankSlotBlocks
              decider symbols).map
                RetainedDirectClauseOccurrenceSlots.ofList)) ++
        retainedDirectClauseRouteTailRecordQueriesOfSlotInputs
          (List.zip
            (directRetainedFinalRoutedClauseQueries decider symbols)
            ((directSourceFinalRoutedClauseStableRankSlotBlocks
              decider symbols).map
                RetainedDirectClauseOccurrenceSlots.ofList)) ++
          retainedDirectClauseRouteTailRecordQueriesOfSlotInputs
            (List.zip
              (directRetainedFinalRoutedVariableClauseQueries
                decider symbols)
              ((directSourceFinalRoutedVariableStableRankSlotBlocks
                decider symbols).map
                  RetainedDirectClauseOccurrenceSlots.ofList)) := by
  have fallbackNil :
      retainedDirectClauseRouteTailRecordQueriesOfSlotInputs
          (List.zip
            (directRetainedFinalCarrierClauseQueries decider symbols ++
              directRetainedFinalBendClauseQueries decider symbols)
            ((directSourceFinalCarrierStableRankSlotBlocks decider symbols ++
                directSourceFinalBendStableRankSlotBlocks
                  decider symbols).map
              RetainedDirectClauseOccurrenceSlots.ofList)) = [] := by
    unfold directRetainedFinalCarrierClauseQueries
      directRetainedFinalBendClauseQueries
    rw [← retainedFinalPrecomputedClauseQueries_append]
    exact
      retainedDirectClauseRouteTailRecordQueriesOfSlotInputs_zip_precomputed
        _ _
  rw [directSourceFinalClauseRouteTailRecordSlotInputs_eq_families]
  simp only [retainedDirectClauseRouteTailRecordQueriesOfSlotInputs_append]
  rw [fallbackNil]
  simp only [List.append_nil]

end LeanTrominoes.PeriodicCNFStripReduction

end
