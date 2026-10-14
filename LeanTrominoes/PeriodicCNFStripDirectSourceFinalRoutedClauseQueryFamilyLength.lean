/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRoutedClauseQuerySemantics

/-! # Length of the final routed-clause query family -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directFinalRoutedClauseQueryLengthVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

theorem directRetainedFinalRoutedClauseQueries_length
    (symbols : List encoding.Γ) :
    (directRetainedFinalRoutedClauseQueries decider symbols).length =
      (directSourceFinalRoutedClauseClauses decider symbols).length := by
  rw [directRetainedFinalRoutedClauseQueries_eq_indexed]
  rw [directSourceFinalIndexedRoutedClauseQueries_eq_named]
  unfold retainedFinalIndexedClauseQueriesFrom
  simp only [List.length_map, List.length_zipIdx]

end LeanTrominoes.PeriodicCNFStripReduction

end
