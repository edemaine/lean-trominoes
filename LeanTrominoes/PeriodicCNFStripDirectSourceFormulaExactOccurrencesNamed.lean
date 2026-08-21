/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaData
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaExactOccurrences

/-! # Exact occurrences in the named direct source formula -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceExactOccurrencesNamedStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable local instance directSourceExactOccurrencesNamedVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

noncomputable local instance directSourceExactOccurrencesNamedVariableBEq :
    BEq Variable :=
  directSourceVariableBEq

theorem directSourceFormula_variableOccurrences_count_eq_three_of_mem
    (symbols : List encoding.Γ) (atom : Variable)
    (membership : atom ∈
      (directSourceFormula decider symbols).variableOccurrences.dedup) :
    (directSourceFormula decider symbols).variableOccurrences.count atom = 3 := by
  unfold directSourceFormula at membership ⊢
  exact sourceFormula_variableOccurrences_count_eq_three_of_mem
    decider symbols atom membership

end PeriodicCNFStripReduction
end LeanTrominoes
