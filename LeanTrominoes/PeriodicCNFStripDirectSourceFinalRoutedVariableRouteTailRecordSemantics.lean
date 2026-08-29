/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRoutedVariableClauseIndexedMembership
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRoutedVariableTerminalChoices
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalScaledTerminalCertificate
import LeanTrominoes.RetainedAngularFanDirectClauseGlobalStableRankAttachmentListSemantics

/-! # Semantic final routed-variable route-tail records -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalRoutedVariableRouteTailSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalRoutedVariableRouteTailSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Attaching the routed-variable stable-rank blocks recovers exactly the
semantic route-tail record query for every globally indexed suffix clause. -/
theorem directSourceFinalRoutedVariableRouteTailRecordQueries_eq_semantic
    (symbols : List encoding.Γ) :
    retainedDirectClauseRouteTailRecordQueriesOfSlotInputs
        (List.zip
          (directRetainedFinalRoutedVariableClauseQueries decider symbols)
          ((directSourceFinalRoutedVariableStableRankSlotBlocks
            decider symbols).map
              RetainedDirectClauseOccurrenceSlots.ofList)) =
      ((directSourceFinalRoutedVariableClauses decider symbols).zipIdx
          (directSourceFinalRoutedVariableStart decider symbols)).map
        fun taggedClause =>
          retainedFinalDirectClauseRouteTailRecordQuery
            (directSourceFormula decider symbols)
            taggedClause.2 ⟨(0, 0), taggedClause.1⟩ := by
  rw [directRetainedFinalRoutedVariableClauseQueries_eq_indexed,
    directSourceFinalIndexedRoutedVariableQueries_eq_named,
    ← directSourceFormula_eq_finalNormalized]
  unfold directSourceFinalRoutedVariableStableRankSlotBlocks
    directSourceFinalStableRankSlotBlocksFrom
  rw [List.map_map]
  apply retainedDirectClauseRouteTailRecordQueriesOfGlobalStableRankBlocks
    (directSourceFormula decider symbols)
    (directSourceFinalRoutedVariableStart decider symbols)
    (directSourceFinalRoutedVariableClauses decider symbols)
    (directSourceFinalScaledOccurrenceTerminalCertificate decider symbols)
  · intro taggedClause taggedMember
    rw [directSourceFinalScaledClauses_eq decider symbols]
    simpa only [directSourceFinalRoutedVariableTaggedClauses,
      directSourceFinalRoutedVariableTaggedSourceClauses] using
      directSourceFinalRoutedVariableClauses_indexedMember
        decider symbols taggedClause taggedMember
  · exact directSourceFinalRoutedVariableClauses_nonempty decider symbols
  · exact directSourceFinalRoutedVariableClauses_widthAtMostThree
      decider symbols
  · have routeChoices : FinalIndexedClauseRouteChoices
        (directSourceFormula decider symbols)
        (directSourceFinalRoutedVariableStart decider symbols)
        (directSourceFinalRoutedVariableClauses decider symbols) := by
      rw [directSourceFormula_eq_finalNormalized]
      exact directSourceFinalRoutedVariableRouteChoices decider symbols
    exact routeChoices.choices

end LeanTrominoes.PeriodicCNFStripReduction

end
