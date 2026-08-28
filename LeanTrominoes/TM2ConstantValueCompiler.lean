/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2ConstantListCompiler
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Constant semantic-value compilers -/

noncomputable section

namespace LeanTrominoes.TM2ConstantValueCompiler

open Computability Turing

/-- A fixed semantic value is polynomial-time computable under every finite
input alphabet, including the empty alphabet. -/
noncomputable def computableInPolyTime
    {Input Output InputSymbol OutputSymbol : Type}
    [Fintype InputSymbol] [Fintype OutputSymbol]
    [Inhabited OutputSymbol]
    (encodeInput : Input → List InputSymbol)
    (encodeOutput : Output → List OutputSymbol)
    (output : Output) :
    TM2ComputableInPolyTime encodeInput encodeOutput
      (fun _ : Input => output) :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (TM2ConstantListCompiler.computableInPolyTime
      encodeInput (encodeOutput output))
    (fun _ => rfl)

end LeanTrominoes.TM2ConstantValueCompiler

end
