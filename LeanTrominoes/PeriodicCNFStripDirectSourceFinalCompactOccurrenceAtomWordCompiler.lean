/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFiveFamilyCompactAtomWordCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFiveFamilyCompactAtomWordOccurrenceSemantics

/-! # Compiler for the final compact occurrence atom-word column -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCompactOccurrenceCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The exact final compact occurrence atom-word column is polynomial-time
computable from direct source symbols. -/
noncomputable def
    directSourceFinalCompactOccurrenceAtomWordsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) DelimitedBinaryWords.Input
      encoding.Γ DelimitedBinaryWords.Token
      id DelimitedBinaryWords.finEncoding.encode
      (directSourceFinalCompactOccurrenceAtomWords decider) := by
  rw [← funext
    (directSourceFinalFiveFamilyCompiledCompactAtomWords_eq_occurrence
      decider)]
  exact
    directSourceFinalFiveFamilyCompiledCompactAtomWordsComputableInPolyTime
      decider

end PeriodicCNFStripReduction
end LeanTrominoes

end
