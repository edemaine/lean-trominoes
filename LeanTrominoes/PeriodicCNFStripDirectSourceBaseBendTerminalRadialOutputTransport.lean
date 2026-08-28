/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceBaseBendTerminalRadialStreamCompiler
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Output transport for direct retained-bend terminal radial lengths -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directBaseBendRadialTransportStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Reinterpret the physical stream as its semantic unary radial column. -/
opaque directSourceBaseBendTerminalRadialOutputTransport
    (encodedOutputEq : ∀ symbols,
      directSourceBaseBendTerminalRadialStream decider symbols =
        UnaryFieldEncoderMachine.unaryFields
          (directSourceBaseBendTerminalRadialLengths decider symbols)) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceBaseBendTerminalRadialLengths decider) :=
  TM2PolyTimeOutputEncodingTransport.of_identity_output_eq
    (Input := List encoding.Γ)
    (Output := List Nat)
    (InputSymbol := encoding.Γ)
    (OutputSymbol := UnaryFieldEncoderMachine.Symbol)
    (encodeInput := id)
    (encodeOutput := UnaryFieldEncoderMachine.unaryFields)
    (physicalOutput := directSourceBaseBendTerminalRadialStream decider)
    (function := directSourceBaseBendTerminalRadialLengths decider)
    (directSourceBaseBendTerminalRadialStreamComputableInPolyTime decider)
    encodedOutputEq

end LeanTrominoes.PeriodicCNFStripReduction

end
