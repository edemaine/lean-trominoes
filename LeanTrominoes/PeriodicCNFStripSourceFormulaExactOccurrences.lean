/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripSourceFormula
import LeanTrominoes.PeriodicThreeSATThreeExactOccurrences

/-! # Exact occurrence counts in normalized strip source formulas -/

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

local instance sourceFormulaExactOccurrencesVariableBEq : BEq Variable :=
  instBEqOfDecidableEq

/-- Every variable retained by the occurrence-split normalized formula occurs
exactly three times. -/
theorem normalizedFormula_variableOccurrences_count_eq_three_of_mem
    (source : PeriodicCNF Nat) (atom : Variable)
    (membership :
      atom ∈ (PeriodicCNF.variableOccurrences
        (normalizedFormula source)).dedup) :
    (PeriodicCNF.variableOccurrences
      (normalizedFormula source)).count atom = 3 := by
  exact
    PeriodicThreeSATThree.formula_variableOccurrences_count_eq_three_of_mem_with_beq
      (by infer_instance) (by infer_instance)
      (PeriodicThreeCNF.formula source) atom membership

end PeriodicCNFStripReduction
end LeanTrominoes
