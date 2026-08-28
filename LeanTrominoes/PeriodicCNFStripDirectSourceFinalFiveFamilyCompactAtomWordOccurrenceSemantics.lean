/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFiveFamilyCompactAtomWordCompilerSemantics

/-! # The compiled five-family words are the final occurrence column -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFiveFamilyOccurrenceSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The compiled append tree is the exact final compact occurrence-word
column, not merely a permutation of it. -/
theorem directSourceFinalFiveFamilyCompiledCompactAtomWords_eq_occurrence
    (symbols : List encoding.Γ) :
    directSourceFinalFiveFamilyCompiledCompactAtomWords decider symbols =
      directSourceFinalCompactOccurrenceAtomWords decider symbols := by
  apply DelimitedBinaryWords.eq_of_words_eq
  exact (directSourceFinalFiveFamilyCompiledCompactAtomWords_words
      decider symbols).trans
      (directSourceFinalCompactOccurrenceAtomWords_eq_blocks
        decider symbols).symm

end PeriodicCNFStripReduction
end LeanTrominoes

end
