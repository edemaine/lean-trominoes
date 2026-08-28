/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierTerminalDirectionSuffixCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalDirectTerminalColumnCompiler

/-! # Compiling the complete final terminal-direction column -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalDirectionCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable def directSourceFinalTerminalDirectionRanksComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalTerminalDirectionRanks decider) := by
  change TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
    (fun symbols : List encoding.Γ =>
      directSourceFinalCrossoverTerminalDirectionRanks decider symbols ++
        directSourceFinalCarrierTerminalDirectionRankSuffix decider symbols)
  exact UnaryFieldEncoderMachine.appendComputableInPolyTime
    (directSourceFinalCrossoverTerminalDirectionRanksComputableInPolyTime
      decider)
    (directSourceFinalCarrierTerminalDirectionRankSuffixComputableInPolyTime
      decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
