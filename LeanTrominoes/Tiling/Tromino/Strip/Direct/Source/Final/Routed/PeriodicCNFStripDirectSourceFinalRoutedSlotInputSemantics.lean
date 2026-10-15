/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Occurrence.PeriodicCNFStripDirectSourceFinalOccurrenceRoleSlotInputFamilySemantics
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Crossover.PeriodicCNFStripDirectSourceFinalCrossoverPhaseSemantics
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Fallback.PeriodicCNFStripDirectSourceFinalFallbackPhaseSemantics
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Routed.PeriodicCNFStripDirectSourceFinalRoutedClausePhaseSemantics
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Routed.PeriodicCNFStripDirectSourceFinalRoutedVariablePhaseSemantics
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectClauseRouteTailRecordPhaseFilterSemantics

/-! # Routed phase of direct-source final slot inputs -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


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
