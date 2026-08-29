/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRoutedVariableQuerySemantics

/-! # Length of the final routed-variable query family -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalRoutedVariableQueryLengthStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalRoutedVariableQueryLengthVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

theorem directRetainedFinalRoutedVariableClauseQueries_length
    (symbols : List encoding.Γ) :
    (directRetainedFinalRoutedVariableClauseQueries
        decider symbols).length =
      (directSourceFinalRoutedVariableClauses decider symbols).length := by
  rw [directRetainedFinalRoutedVariableClauseQueries_eq_indexed]
  rw [directSourceFinalIndexedRoutedVariableQueries_eq_named]
  unfold retainedFinalIndexedClauseQueriesFrom
  simp only [List.length_map, List.length_zipIdx]

end LeanTrominoes.PeriodicCNFStripReduction

end
