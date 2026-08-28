/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Complexity

/-! # Transporting polynomial-time machines across output encodings -/

noncomputable section

namespace LeanTrominoes
namespace TM2PolyTimeOutputEncodingTransport

open Computability Turing

/-- Reinterpret a polynomial-time machine at another semantic codomain when
the two requested outputs have exactly the same finite encoding. -/
opaque of_encoded_output_eq
    {Input Output₁ Output₂ InputSymbol OutputSymbol : Type}
    {encodeInput : Input → List InputSymbol}
    {encodeOutput₁ : Output₁ → List OutputSymbol}
    {encodeOutput₂ : Output₂ → List OutputSymbol}
    {function₁ : Input → Output₁} {function₂ : Input → Output₂}
    (compiler :
      TM2ComputableInPolyTime encodeInput encodeOutput₁ function₁)
    (encodedOutputEq : ∀ input,
      encodeOutput₁ (function₁ input) =
        encodeOutput₂ (function₂ input)) :
    TM2ComputableInPolyTime encodeInput encodeOutput₂ function₂ := by
  exact {
    tm := compiler.tm
    inputAlphabet := compiler.inputAlphabet
    outputAlphabet := compiler.outputAlphabet
    time := compiler.time
    outputsFun input := by
      rw [← encodedOutputEq input]
      exact compiler.outputsFun input
  }

/-- Specialization for a physical symbol-list output whose encoding is the
identity.  Keeping this boundary opaque avoids repeatedly normalizing the
identity encoding through a composed compiler. -/
opaque of_identity_output_eq
    {Input Output InputSymbol OutputSymbol : Type}
    {encodeInput : Input → List InputSymbol}
    {encodeOutput : Output → List OutputSymbol}
    {physicalOutput : Input → List OutputSymbol}
    {function : Input → Output}
    (compiler :
      TM2ComputableInPolyTime encodeInput id physicalOutput)
    (encodedOutputEq : ∀ input,
      physicalOutput input = encodeOutput (function input)) :
    TM2ComputableInPolyTime encodeInput encodeOutput function :=
  of_encoded_output_eq
    (encodeOutput₁ := id)
    compiler encodedOutputEq

end TM2PolyTimeOutputEncodingTransport
end LeanTrominoes
