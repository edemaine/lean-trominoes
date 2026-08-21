/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaFacts
import LeanTrominoes.PeriodicCNFStripSourceFormulaExactOccurrences

/-! # Exact occurrence counts in the direct strip source formula -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF

local instance directSourceExactOccurrencesVariableBEq : BEq Variable :=
  instBEqOfDecidableEq

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceExactOccurrencesStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Every variable retained by the generated direct source formula occurs
exactly three times. -/
theorem sourceFormula_variableOccurrences_count_eq_three_of_mem
    (symbols : List encoding.Γ) (atom : Variable)
    (membership :
      atom ∈ (PeriodicCNF.variableOccurrences
        (sourceFormula
          (PolySpaceCompiler.formulaOfSymbols decider symbols))).dedup) :
    (PeriodicCNF.variableOccurrences
      (sourceFormula
        (PolySpaceCompiler.formulaOfSymbols decider symbols))).count atom = 3 := by
  rw [sourceFormula_formulaOfSymbols] at membership ⊢
  exact normalizedFormula_variableOccurrences_count_eq_three_of_mem
    (PolySpaceCompiler.formulaOfSymbols decider symbols) atom membership

end PeriodicCNFStripReduction
end LeanTrominoes
