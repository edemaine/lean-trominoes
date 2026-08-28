/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierTerminalRadialCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendRoutedTerminalRadialCompiler

/-! # Compiling the final carrier/bend/routed radial suffix -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierRadialSuffixStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable def
    directSourceFinalCarrierTerminalRadialSuffixComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalCarrierTerminalRadialSuffix decider) := by
  change TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
    (fun symbols : List encoding.Γ =>
      directSourceCarrierTerminalRadialLengths decider symbols ++
        directSourceFinalBendRoutedTerminalRadialLengths decider symbols)
  exact UnaryFieldEncoderMachine.appendComputableInPolyTime
    (directSourceCarrierTerminalRadialLengthsComputableInPolyTime decider)
    (directSourceFinalBendRoutedTerminalRadialLengthsComputableInPolyTime
      decider)

end LeanTrominoes.PeriodicCNFStripReduction

end

