/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Transporting polynomial-time compilers across function equality -/

noncomputable section

namespace LeanTrominoes.TM2PolyTimeFunctionTransport

open Computability Turing

/-- Reinterpret a compiler at a pointwise equal semantic function. -/
opaque of_output_eq
    {Input Output InputSymbol OutputSymbol : Type}
    {encodeInput : Input → List InputSymbol}
    {encodeOutput : Output → List OutputSymbol}
    {first second : Input → Output}
    (compiler : TM2ComputableInPolyTime encodeInput encodeOutput first)
    (outputEq : ∀ input, first input = second input) :
    TM2ComputableInPolyTime encodeInput encodeOutput second :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    compiler (fun input => congrArg encodeOutput (outputEq input))

end LeanTrominoes.TM2PolyTimeFunctionTransport

end
