/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierCompactAtomWordBlockCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierCompactAtomWordBlockSemantics

/-! # Compiler for the final direct carrier compact atom-word block -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directCarrierCompactFinalBlockStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The exact final carrier compact word block is polynomial-time computable
from direct source symbols. -/
noncomputable def
    directSourceFinalCompactCarrierAtomWordsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) DelimitedBinaryWords.Input
      encoding.Γ DelimitedBinaryWords.Token
      id DelimitedBinaryWords.finEncoding.encode
      (directSourceFinalCompactCarrierAtomWords decider) := by
  rw [← funext
    (directSourceCarrierCompactAtomWordBlock_eq_finalBlock decider)]
  exact directSourceCarrierCompactAtomWordBlockComputableInPolyTime decider

end PeriodicCNFStripReduction
end LeanTrominoes

end
