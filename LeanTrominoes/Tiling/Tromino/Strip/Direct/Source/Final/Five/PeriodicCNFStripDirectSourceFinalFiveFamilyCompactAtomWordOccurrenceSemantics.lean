/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Five.PeriodicCNFStripDirectSourceFinalFiveFamilyCompactAtomWordCompilerSemantics

/-! # The compiled five-family words are the final occurrence column -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


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
