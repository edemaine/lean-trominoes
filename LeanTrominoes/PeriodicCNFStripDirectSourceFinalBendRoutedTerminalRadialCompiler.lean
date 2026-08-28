/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceBaseBendTerminalRadialCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalDirectTerminalColumnCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalTerminalColumnData
import LeanTrominoes.UnaryFieldEncoderAppendClosure

/-! # Compiling the final bend/routed terminal-radial suffix -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalBendRoutedRadialStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable def
    directSourceFinalBendRoutedTerminalRadialLengthsComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalBendRoutedTerminalRadialLengths decider) := by
  change TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
    (fun symbols : List encoding.Γ =>
      directSourceBaseBendTerminalRadialLengths decider symbols ++
        directSourceFinalRoutedTerminalRadialLengths decider symbols)
  exact UnaryFieldEncoderMachine.appendComputableInPolyTime
    (directSourceBaseBendTerminalRadialLengthsComputableInPolyTime decider)
    (directSourceFinalRoutedTerminalRadialLengthsComputableInPolyTime decider)

end LeanTrominoes.PeriodicCNFStripReduction

end

