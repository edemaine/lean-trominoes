/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceRoutedClauseCompactAtomWordSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceTerminalCompactAtomWordCompiler

/-! # Compiler for direct routed-clause compact atom words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRoutedClauseCompactWordCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The exact routed-clause compact word block is polynomial-time
computable from direct source symbols. -/
noncomputable def
    directSourceFinalCompactRoutedClauseAtomWordsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) DelimitedBinaryWords.Input
      encoding.Γ DelimitedBinaryWords.Token
      id DelimitedBinaryWords.finEncoding.encode
      (directSourceFinalCompactRoutedClauseAtomWords decider) := by
  rw [← funext
    (directSourceTerminalCompactAtomWords_eq_routedClauseBlock decider)]
  exact directSourceTerminalCompactAtomWordsComputableInPolyTime decider

end PeriodicCNFStripReduction
end LeanTrominoes

end
