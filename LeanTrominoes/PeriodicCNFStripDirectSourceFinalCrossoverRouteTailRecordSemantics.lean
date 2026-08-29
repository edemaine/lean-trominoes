/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCrossoverClauseIndexedMembership
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCrossoverTerminalChoices
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalScaledTerminalCertificate
import LeanTrominoes.RetainedAngularFanDirectClauseGlobalStableRankAttachmentListSemantics

/-! # Semantic final crossover route-tail records -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCrossoverRouteTailSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCrossoverRouteTailSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Attaching the crossover stable-rank blocks recovers exactly the
semantic route-tail record query for every globally indexed crossover. -/
theorem directSourceFinalCrossoverRouteTailRecordQueries_eq_semantic
    (symbols : List encoding.Γ) :
    retainedDirectClauseRouteTailRecordQueriesOfSlotInputs
        (List.zip
          (directRetainedFinalCrossoverClauseQueries decider symbols)
          ((directSourceFinalCrossoverStableRankSlotBlocks
            decider symbols).map
              RetainedDirectClauseOccurrenceSlots.ofList)) =
      ((directSourceFinalCrossoverClauses decider symbols).zipIdx 0).map
        fun taggedClause =>
          retainedFinalDirectClauseRouteTailRecordQuery
            (directSourceFormula decider symbols)
            taggedClause.2 ⟨(0, 0), taggedClause.1⟩ := by
  rw [directRetainedFinalCrossoverClauseQueries_eq_indexed]
  unfold directSourceFinalCrossoverStableRankSlotBlocks
    directSourceFinalStableRankSlotBlocksFrom
  rw [List.map_map]
  apply retainedDirectClauseRouteTailRecordQueriesOfGlobalStableRankBlocks
    (directSourceFormula decider symbols)
    0
    (directSourceFinalCrossoverClauses decider symbols)
    (directSourceFinalScaledOccurrenceTerminalCertificate decider symbols)
  · intro taggedClause taggedMember
    rw [directSourceFinalScaledClauses_eq decider symbols]
    simpa only [directSourceFinalCrossoverTaggedClauses,
      directSourceFinalCrossoverTaggedSourceClauses] using
      directSourceFinalCrossoverClauses_indexedMember
        decider symbols taggedClause taggedMember
  · exact directSourceFinalCrossoverClauses_nonempty decider symbols
  · exact directSourceFinalCrossoverClauses_widthAtMostThree
      decider symbols
  · exact (directSourceFinalCrossoverRouteChoices
      decider symbols).choices

end LeanTrominoes.PeriodicCNFStripReduction

end
