/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCrossoverClauseQuerySemantics

/-! # Length of the final crossover query family -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCrossoverQueryLengthStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCrossoverQueryLengthVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

theorem directRetainedFinalCrossoverClauseQueries_length
    (symbols : List encoding.Γ) :
    (directRetainedFinalCrossoverClauseQueries decider symbols).length =
      (directSourceFinalCrossoverClauses decider symbols).length := by
  rw [directRetainedFinalCrossoverClauseQueries_eq_indexed]
  unfold retainedFinalIndexedClauseQueriesFrom
  simp only [List.length_map, List.length_zipIdx]

end LeanTrominoes.PeriodicCNFStripReduction

end
