/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FixedAxisUnaryFieldsCompiler
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Exact compilation of fixed-axis unary fields -/

noncomputable section

namespace LeanTrominoes.FixedAxisUnaryFields

open Computability Turing

/-- An exact-length activation compiler emits the canonical unary encoding
of its active-horizontal zero-or-one values. -/
noncomputable def afterExactComputableInPolyTime
    {Input InputSymbol : Type}
    (encodeInput : Input → List InputSymbol)
    (axes : List Bool) (activations : Input → List Bool)
    (activationCompiler :
      TM2ComputableInPolyTime encodeInput id activations)
    (lengthEq : ∀ input, (activations input).length = axes.length) :
    TM2ComputableInPolyTime encodeInput
      UnaryFieldEncoderMachine.unaryFields
      (fun input => values axes (activations input)) := by
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (afterComputableInPolyTime encodeInput axes activations
      activationCompiler)
    (fun input => compiledFields_eq axes (activations input)
      (lengthEq input))

end LeanTrominoes.FixedAxisUnaryFields

end
