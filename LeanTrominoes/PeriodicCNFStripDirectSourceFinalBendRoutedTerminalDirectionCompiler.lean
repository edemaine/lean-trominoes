/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceBaseBendTerminalDirectionCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalDirectTerminalColumnCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalTerminalColumnData
import LeanTrominoes.UnaryFieldEncoderAppendClosure

/-! # Compiling the final bend/routed terminal-direction suffix -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalBendRoutedDirectionStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable def
    directSourceFinalBendRoutedTerminalDirectionRanksComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalBendRoutedTerminalDirectionRanks decider) := by
  change TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
    (fun symbols : List encoding.Γ =>
      directSourceBaseBendTerminalDirectionRanks decider symbols ++
        directSourceFinalRoutedTerminalDirectionRanks decider symbols)
  exact UnaryFieldEncoderMachine.appendComputableInPolyTime
    (directSourceBaseBendTerminalDirectionRanksComputableInPolyTime decider)
    (directSourceFinalRoutedTerminalDirectionRanksComputableInPolyTime decider)

end LeanTrominoes.PeriodicCNFStripReduction

end

