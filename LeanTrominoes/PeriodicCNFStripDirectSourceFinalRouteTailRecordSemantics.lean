/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCrossoverRouteTailRecordSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRouteTailRecordData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRouteTailRecordQueryFamilySemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRoutedClauseRouteTailRecordSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRoutedVariableRouteTailRecordSemantics

/-! # Semantic direct-source final route-tail record stream -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalRouteTailSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalRouteTailSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The complete successful attachment stream consists of the semantic
crossover prefix followed by the routed-clause and routed-variable blocks. -/
theorem directSourceFinalClauseRouteTailRecordQueries_eq_semantic
    (symbols : List encoding.Γ) :
    retainedDirectClauseRouteTailRecordQueriesOfSlotInputs
        (directSourceFinalClauseRouteTailRecordSlotInputs decider symbols) =
      ((directSourceFinalCrossoverClauses decider symbols).zipIdx 0).map
          (fun taggedClause =>
            retainedFinalDirectClauseRouteTailRecordQuery
              (directSourceFormula decider symbols)
              taggedClause.2 ⟨(0, 0), taggedClause.1⟩) ++
        ((directSourceFinalRoutedClauseClauses decider symbols).zipIdx
            (directSourceFinalRoutedClauseStart decider symbols)).map
            (fun taggedClause =>
              retainedFinalDirectClauseRouteTailRecordQuery
                (directSourceFormula decider symbols)
                taggedClause.2 ⟨(0, 0), taggedClause.1⟩) ++
          ((directSourceFinalRoutedVariableClauses decider symbols).zipIdx
              (directSourceFinalRoutedVariableStart decider symbols)).map
              fun taggedClause =>
                retainedFinalDirectClauseRouteTailRecordQuery
                  (directSourceFormula decider symbols)
                  taggedClause.2 ⟨(0, 0), taggedClause.1⟩ := by
  rw [directSourceFinalClauseRouteTailRecordQueries_eq_directFamilies,
    directSourceFinalCrossoverRouteTailRecordQueries_eq_semantic,
    directSourceFinalRoutedClauseRouteTailRecordQueries_eq_semantic,
    directSourceFinalRoutedVariableRouteTailRecordQueries_eq_semantic]

/-- Consequently the compiled flat record word has the same three semantic
family blocks, with carrier and bend records deliberately left for insertion
between the first and second blocks. -/
theorem directSourceFinalClauseRouteTailRecordTokens_eq_semantic
    (symbols : List encoding.Γ) :
    directSourceFinalClauseRouteTailRecordTokens decider symbols =
      retainedDirectClauseRouteTailRecordStream
          (((directSourceFinalCrossoverClauses decider symbols).zipIdx 0).map
            fun taggedClause =>
              retainedFinalDirectClauseRouteTailRecordQuery
                (directSourceFormula decider symbols)
                taggedClause.2 ⟨(0, 0), taggedClause.1⟩) ++
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
  unfold directSourceFinalClauseRouteTailRecordTokens
    retainedDirectClauseRouteTailRecordStream
  rw [directSourceFinalClauseRouteTailRecordQueries_eq_semantic]
  simp only [List.flatMap_append]

end LeanTrominoes.PeriodicCNFStripReduction

end
