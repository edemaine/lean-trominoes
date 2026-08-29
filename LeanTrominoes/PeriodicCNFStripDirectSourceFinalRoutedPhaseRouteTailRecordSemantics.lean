/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalPhaseRouteTailRecordData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRoutedClauseRouteTailRecordSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRoutedSlotInputSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRoutedVariableRouteTailRecordSemantics
import LeanTrominoes.RetainedAngularFanDirectClauseRouteTailRecordSlotAttachmentListSemantics

/-! # Semantics of the direct-source routed route-tail phase -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalRoutedPhaseRouteTailStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalRoutedPhaseRouteTailVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The filtered routed token stream is exactly the routed-clause semantic
record word followed by the routed-variable semantic record word. -/
theorem directSourceFinalRoutedRouteTailRecordTokens_eq_semantic
    (symbols : List encoding.Γ) :
    directSourceFinalRoutedRouteTailRecordTokens decider symbols =
      retainedDirectClauseRouteTailRecordStream
          (((directSourceFinalRoutedClauseClauses decider symbols).zipIdx
              (directSourceFinalRoutedClauseStart decider symbols)).map
            fun taggedClause =>
              retainedFinalDirectClauseRouteTailRecordQuery
                (directSourceFormula decider symbols)
                taggedClause.2 ⟨(0, 0), taggedClause.1⟩) ++
        retainedDirectClauseRouteTailRecordStream
          (((directSourceFinalRoutedVariableClauses decider symbols).zipIdx
              (directSourceFinalRoutedVariableStart decider symbols)).map
            fun taggedClause =>
              retainedFinalDirectClauseRouteTailRecordQuery
                (directSourceFormula decider symbols)
                taggedClause.2 ⟨(0, 0), taggedClause.1⟩) := by
  unfold directSourceFinalRoutedRouteTailRecordTokens
    directSourceFinalRoutedRouteTailRecordSlotInputs
  rw [retainedDirectRoutedRouteTailRecordSlotInputs_directSource_eq]
  simp only [retainedDirectClauseRouteTailRecordQueriesOfSlotInputs_append]
  rw [directSourceFinalRoutedClauseRouteTailRecordQueries_eq_semantic,
    directSourceFinalRoutedVariableRouteTailRecordQueries_eq_semantic]
  unfold retainedDirectClauseRouteTailRecordStream
  simp only [List.flatMap_append]

end LeanTrominoes.PeriodicCNFStripReduction

end
