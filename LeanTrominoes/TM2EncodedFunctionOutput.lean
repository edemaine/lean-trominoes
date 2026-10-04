/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Reinterpret an emitted encoding without evaluating its semantic value -/
noncomputable section
namespace LeanTrominoes.TM2PolyTimeOutputEncodingTransport
open _root_.Computability Turing

def of_encoded_function {Input Output InputSymbol OutputSymbol : Type}
    (encodeInput : Input → List InputSymbol) (encodeOutput : Output → List OutputSymbol)
    (function : Input → Output)
    (compiler : TM2ComputableInPolyTime encodeInput id (fun input => encodeOutput (function input))) :
    TM2ComputableInPolyTime encodeInput encodeOutput function :=
  of_encoded_output_eq (encodeOutput₂ := encodeOutput) (function₂ := function) compiler (fun _ => rfl)
end LeanTrominoes.TM2PolyTimeOutputEncodingTransport
