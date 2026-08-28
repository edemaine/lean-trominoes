/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCompactBendRoutedSuffixAtomWordCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCompactCrossoverCarrierAtomWordCompiler

/-! # Compiler for all five compact atom-word families -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFiveFamilyCompactCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The exact five-family compact atom-word append tree is polynomial-time
computable from direct source symbols. -/
noncomputable def
    directSourceFinalFiveFamilyCompiledCompactAtomWordsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) DelimitedBinaryWords.Input
      encoding.Γ DelimitedBinaryWords.Token
      id DelimitedBinaryWords.finEncoding.encode
      (directSourceFinalFiveFamilyCompiledCompactAtomWords decider) := by
  change @TM2ComputableInPolyTime
    (List encoding.Γ) DelimitedBinaryWords.Input
    encoding.Γ DelimitedBinaryWords.Token
    id DelimitedBinaryWords.finEncoding.encode
    (fun symbols => DelimitedBinaryWords.append
      (directSourceFinalCompactCrossoverCarrierAtomWords decider symbols)
      (directSourceFinalCompactBendRoutedSuffixAtomWords decider symbols))
  exact DelimitedBinaryWords.appendComputableInPolyTime
    (directSourceFinalCompactCrossoverCarrierAtomWordsComputableInPolyTime
      decider)
    (directSourceFinalCompactBendRoutedSuffixAtomWordsComputableInPolyTime
      decider)

end PeriodicCNFStripReduction
end LeanTrominoes

end
