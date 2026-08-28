/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceBendCompactAtomWordBlockSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceBendCompactAtomWordCompiler

/-! # Compiler for the final direct bend compact atom-word block -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directBendCompactBlockCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The exact final bend compact word block is polynomial-time computable
from direct source symbols. -/
noncomputable def directSourceFinalCompactBendAtomWordsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) DelimitedBinaryWords.Input
      encoding.Γ DelimitedBinaryWords.Token
      id DelimitedBinaryWords.finEncoding.encode
      (directSourceFinalCompactBendAtomWords decider) := by
  rw [← funext
    (directSourceBendCompactAtomWords_eq_finalBlock decider)]
  exact directSourceBendCompactAtomWordsComputableInPolyTime decider

end PeriodicCNFStripReduction
end LeanTrominoes

end
