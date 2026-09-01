/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteAlphabetKeyedValueLookupSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidenceSuffixCompiler

/-! # Semantics of sparse variable-incidence suffix selection -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Declarative query-major sparse suffix selection. -/
def directSourceFinalGroupedVariableIncidenceSparseSuffixTokensExpected
    (symbols : List encoding.Γ) :
    List VariableIncidenceSparseSuffixToken :=
  FiniteAlphabetKeyedValueLookup.expected
    (directSourceFinalGroupedVariableIncidenceKeys decider symbols)
    (directSourceFinalGroupedVariableIncidenceSuffixCandidateKeys
      decider symbols)
    (directSourceFinalGroupedVariableIncidenceSuffixCandidateValues
      decider symbols)

/-- The physical finite keyed selector is exactly ordinary query-major
selection from the routed candidates followed by the full default column. -/
theorem directSourceFinalGroupedVariableIncidenceSparseSuffixTokens_eq_expected
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedVariableIncidenceSparseSuffixTokens
        decider symbols =
      directSourceFinalGroupedVariableIncidenceSparseSuffixTokensExpected
        decider symbols := by
  unfold directSourceFinalGroupedVariableIncidenceSparseSuffixTokens
    directSourceFinalGroupedVariableIncidenceSparseSuffixTokensExpected
  apply FiniteAlphabetKeyedValueLookup.values_eq_expected
  rw [directSourceFinalGroupedVariableIncidenceSuffixCandidateKeys_length,
    directSourceFinalGroupedVariableIncidenceSuffixCandidateValues_length]

/-- Erasing routed block ends from that exact selection gives the declared
full suffix token stream. -/
theorem directSourceFinalGroupedVariableIncidenceSuffixDirectionTokens_eq_expected
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedVariableIncidenceSuffixDirectionTokens
        decider symbols =
      VariableIncidenceSparseSuffixToken.output
        (directSourceFinalGroupedVariableIncidenceSparseSuffixTokensExpected
          decider symbols) := by
  unfold directSourceFinalGroupedVariableIncidenceSuffixDirectionTokens
  rw [directSourceFinalGroupedVariableIncidenceSparseSuffixTokens_eq_expected]

end LeanTrominoes.PeriodicCNFStripReduction

end
