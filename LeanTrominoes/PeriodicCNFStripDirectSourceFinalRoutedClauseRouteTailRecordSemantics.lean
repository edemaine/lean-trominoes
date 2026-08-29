/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRoutedClauseIndexedMembership
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRoutedClauseTerminalChoices
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalScaledTerminalCertificate
import LeanTrominoes.RetainedAngularFanDirectClauseGlobalStableRankAttachmentListSemantics

/-! # Semantic final routed-clause route-tail records -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalRoutedClauseRouteTailSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalRoutedClauseRouteTailSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Attaching the routed-clause stable-rank blocks recovers exactly the
semantic route-tail record query for every globally indexed source clause. -/
theorem directSourceFinalRoutedClauseRouteTailRecordQueries_eq_semantic
    (symbols : List encoding.Γ) :
    retainedDirectClauseRouteTailRecordQueriesOfSlotInputs
        (List.zip
          (directRetainedFinalRoutedClauseQueries decider symbols)
          ((directSourceFinalRoutedClauseStableRankSlotBlocks
            decider symbols).map
              RetainedDirectClauseOccurrenceSlots.ofList)) =
      ((directSourceFinalRoutedClauseClauses decider symbols).zipIdx
          (directSourceFinalRoutedClauseStart decider symbols)).map
        fun taggedClause =>
          retainedFinalDirectClauseRouteTailRecordQuery
            (directSourceFormula decider symbols)
            taggedClause.2 ⟨(0, 0), taggedClause.1⟩ := by
  rw [directRetainedFinalRoutedClauseQueries_eq_indexed,
    directSourceFinalIndexedRoutedClauseQueries_eq_named,
    ← directSourceFormula_eq_finalNormalized]
  unfold directSourceFinalRoutedClauseStableRankSlotBlocks
    directSourceFinalStableRankSlotBlocksFrom
  rw [List.map_map]
  apply retainedDirectClauseRouteTailRecordQueriesOfGlobalStableRankBlocks
    (directSourceFormula decider symbols)
    (directSourceFinalRoutedClauseStart decider symbols)
    (directSourceFinalRoutedClauseClauses decider symbols)
    (directSourceFinalScaledOccurrenceTerminalCertificate decider symbols)
  · intro taggedClause taggedMember
    rw [directSourceFinalScaledClauses_eq decider symbols]
    simpa only [directSourceFinalRoutedClauseTaggedClauses,
      directSourceFinalRoutedClauseTaggedSourceClauses] using
      directSourceFinalRoutedClauseClauses_indexedMember
        decider symbols taggedClause taggedMember
  · exact directSourceFinalRoutedClauseClauses_nonempty decider symbols
  · exact directSourceFinalRoutedClauseClauses_widthAtMostThree
      decider symbols
  · have routeChoices : FinalIndexedClauseRouteChoices
        (directSourceFormula decider symbols)
        (directSourceFinalRoutedClauseStart decider symbols)
        (directSourceFinalRoutedClauseClauses decider symbols) := by
      rw [directSourceFormula_eq_finalNormalized]
      exact directSourceFinalRoutedClauseRouteChoices decider symbols
    exact routeChoices.choices

end LeanTrominoes.PeriodicCNFStripReduction

end
