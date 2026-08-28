/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierTerminalDirectionCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendRoutedTerminalDirectionCompiler

/-! # Compiling the final carrier/bend/routed direction suffix -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierDirectionSuffixStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable def
    directSourceFinalCarrierTerminalDirectionRankSuffixComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalCarrierTerminalDirectionRankSuffix decider) := by
  change TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
    (fun symbols : List encoding.Γ =>
      directSourceCarrierTerminalDirectionRanks decider symbols ++
        directSourceFinalBendRoutedTerminalDirectionRanks decider symbols)
  exact UnaryFieldEncoderMachine.appendComputableInPolyTime
    (directSourceCarrierTerminalDirectionRanksComputableInPolyTime decider)
    (directSourceFinalBendRoutedTerminalDirectionRanksComputableInPolyTime
      decider)

end LeanTrominoes.PeriodicCNFStripReduction

end

