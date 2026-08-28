/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierTerminalRadialStreamCompiler
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Output transport for direct carrier terminal radial lengths -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceCarrierTerminalRadialTransportStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Reinterpret the physical terminal-radial stream as its exact unary
natural column once their encoded outputs are identified. -/
opaque directSourceCarrierTerminalRadialOutputTransport
    (encodedOutputEq : ∀ symbols,
      directSourceCarrierTerminalRadialStream decider symbols =
        UnaryFieldEncoderMachine.unaryFields
          (directSourceCarrierTerminalRadialLengths decider symbols)) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceCarrierTerminalRadialLengths decider) :=
  TM2PolyTimeOutputEncodingTransport.of_identity_output_eq
    (Input := List encoding.Γ)
    (Output := List Nat)
    (InputSymbol := encoding.Γ)
    (OutputSymbol := UnaryFieldEncoderMachine.Symbol)
    (encodeInput := id)
    (encodeOutput := UnaryFieldEncoderMachine.unaryFields)
    (physicalOutput := directSourceCarrierTerminalRadialStream decider)
    (function := directSourceCarrierTerminalRadialLengths decider)
    (directSourceCarrierTerminalRadialStreamComputableInPolyTime decider)
    encodedOutputEq

end PeriodicCNFStripReduction
end LeanTrominoes

end
