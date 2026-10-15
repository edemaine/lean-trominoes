/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Five.PeriodicCNFStripDirectSourceFinalFiveFamilyCompactAtomWordCompilerData

/-! # Semantics of the compiled five-family compact append tree -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


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
