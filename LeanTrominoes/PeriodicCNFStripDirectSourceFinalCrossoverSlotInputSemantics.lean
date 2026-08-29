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

/-! # Crossover phase of direct-source final slot inputs -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCrossoverSlotInputStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Filtering the complete direct-source slot stream for crossovers recovers
exactly the fixed crossover query/slot prefix. -/
theorem retainedDirectCrossoverRouteTailRecordSlotInputs_directSource_eq
    (symbols : List encoding.Γ) :
    retainedDirectCrossoverRouteTailRecordSlotInputs
        (directSourceFinalClauseRouteTailRecordSlotInputs decider symbols) =
      List.zip
        (directRetainedFinalCrossoverClauseQueries decider symbols)
        ((directSourceFinalCrossoverStableRankSlotBlocks
          decider symbols).map
            RetainedDirectClauseOccurrenceSlots.ofList) := by
  rw [directSourceFinalClauseRouteTailRecordSlotInputs_eq_families]
  simp only [retainedDirectCrossoverRouteTailRecordSlotInputs_append]
  rw [retainedDirectCrossoverRouteTailRecordSlotInputs_zip_eq_self _ _
    (directRetainedFinalCrossoverClauseQueries_isDirectCrossover
      decider symbols)]
  rw [retainedDirectCrossoverRouteTailRecordSlotInputs_zip_eq_nil]
  · rw [retainedDirectCrossoverRouteTailRecordSlotInputs_zip_eq_nil _ _
      (directRetainedFinalRoutedClauseQueries_notDirectCrossover
        decider symbols)]
    rw [retainedDirectCrossoverRouteTailRecordSlotInputs_zip_eq_nil _ _
      (directRetainedFinalRoutedVariableClauseQueries_notDirectCrossover
        decider symbols)]
    simp
  · intro query queryMember
    simp only [List.mem_append] at queryMember
    rcases queryMember with queryMember | queryMember
    · exact directRetainedFinalCarrierClauseQueries_notDirectCrossover
        decider symbols query queryMember
    · exact directRetainedFinalBendClauseQueries_notDirectCrossover
        decider symbols query queryMember

end LeanTrominoes.PeriodicCNFStripReduction

end
