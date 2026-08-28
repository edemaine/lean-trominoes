/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceBendCompactAtomWordBlockCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFiveFamilyCompactAtomWordCompilerData
import LeanTrominoes.PeriodicCNFStripDirectSourceRoutedClauseCompactAtomWordCompiler

/-! # Compiler for the bend/routed-clause compact block -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directCompactBendRoutedClauseStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The bend and routed-clause compact atom-word families are
polynomial-time computable. -/
noncomputable def
    directSourceFinalCompactBendRoutedClauseAtomWordsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) DelimitedBinaryWords.Input
      encoding.Γ DelimitedBinaryWords.Token
      id DelimitedBinaryWords.finEncoding.encode
      (directSourceFinalCompactBendRoutedClauseAtomWords decider) := by
  change @TM2ComputableInPolyTime
    (List encoding.Γ) DelimitedBinaryWords.Input
    encoding.Γ DelimitedBinaryWords.Token
    id DelimitedBinaryWords.finEncoding.encode
    (fun symbols => DelimitedBinaryWords.append
      (directSourceFinalCompactBendAtomWords decider symbols)
      (directSourceFinalCompactRoutedClauseAtomWords decider symbols))
  exact DelimitedBinaryWords.appendComputableInPolyTime
    (directSourceFinalCompactBendAtomWordsComputableInPolyTime decider)
    (directSourceFinalCompactRoutedClauseAtomWordsComputableInPolyTime
      decider)

end PeriodicCNFStripReduction
end LeanTrominoes

end
