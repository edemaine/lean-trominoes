/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFiveFamilyCompactAtomWordCompilerData

/-! # Semantics of the compiled five-family compact append tree -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFiveFamilyCompactSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFiveFamilyCompactSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The physical append tree has exactly the official five-family compact
word list. -/
theorem directSourceFinalFiveFamilyCompiledCompactAtomWords_words
    (symbols : List encoding.Γ) :
    (directSourceFinalFiveFamilyCompiledCompactAtomWords
      decider symbols).words =
      directSourceFinalFiveFamilyCompactAtomWordBlocks decider symbols := by
  unfold directSourceFinalFiveFamilyCompiledCompactAtomWords
    directSourceFinalCompactCrossoverCarrierAtomWords
    directSourceFinalCompactBendRoutedSuffixAtomWords
    directSourceFinalCompactBendRoutedClauseAtomWords
  simp only [DelimitedBinaryWords.append_words]
  rw [directSourceFinalCompactCrossoverAtomWords_eq_block]
  unfold directSourceFinalCompactCarrierAtomWords
    directSourceFinalCompactBendAtomWords
    directSourceFinalCompactRoutedClauseAtomWords
    directSourceFinalRoutedVariableCompactAtomWords
    directSourceFinalFiveFamilyCompactAtomWordBlocks
  simp only

end PeriodicCNFStripReduction
end LeanTrominoes

end
