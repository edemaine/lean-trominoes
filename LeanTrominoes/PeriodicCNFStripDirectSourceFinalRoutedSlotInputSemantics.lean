/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceRoleSlotInputFamilySemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCrossoverPhaseSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFallbackPhaseSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRoutedClausePhaseSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRoutedVariablePhaseSemantics
import LeanTrominoes.RetainedAngularFanDirectClauseRouteTailRecordPhaseFilterSemantics

/-! # Routed phase of direct-source final slot inputs -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalRoutedSlotInputStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Filtering the complete direct-source slot stream for routed clauses
recovers the routed-clause block followed by the routed-variable block. -/
theorem retainedDirectRoutedRouteTailRecordSlotInputs_directSource_eq
    (symbols : List encoding.Γ) :
    retainedDirectRoutedRouteTailRecordSlotInputs
        (directSourceFinalClauseRouteTailRecordSlotInputs decider symbols) =
      List.zip
          (directRetainedFinalRoutedClauseQueries decider symbols)
          ((directSourceFinalRoutedClauseStableRankSlotBlocks
            decider symbols).map
              RetainedDirectClauseOccurrenceSlots.ofList) ++
        List.zip
          (directRetainedFinalRoutedVariableClauseQueries decider symbols)
          ((directSourceFinalRoutedVariableStableRankSlotBlocks
            decider symbols).map
              RetainedDirectClauseOccurrenceSlots.ofList) := by
  rw [directSourceFinalClauseRouteTailRecordSlotInputs_eq_families]
  simp only [retainedDirectRoutedRouteTailRecordSlotInputs_append]
  rw [retainedDirectRoutedRouteTailRecordSlotInputs_zip_eq_nil _ _
    (directRetainedFinalCrossoverClauseQueries_notDirectRouted
      decider symbols)]
  rw [retainedDirectRoutedRouteTailRecordSlotInputs_zip_eq_nil]
  · rw [retainedDirectRoutedRouteTailRecordSlotInputs_zip_eq_self _ _
      (directRetainedFinalRoutedClauseQueries_isDirectRouted
        decider symbols)]
    rw [retainedDirectRoutedRouteTailRecordSlotInputs_zip_eq_self _ _
      (directRetainedFinalRoutedVariableClauseQueries_isDirectRouted
        decider symbols)]
    simp
  · intro query queryMember
    simp only [List.mem_append] at queryMember
    rcases queryMember with queryMember | queryMember
    · exact directRetainedFinalCarrierClauseQueries_notDirectRouted
        decider symbols query queryMember
    · exact directRetainedFinalBendClauseQueries_notDirectRouted
        decider symbols query queryMember

end LeanTrominoes.PeriodicCNFStripReduction

end
