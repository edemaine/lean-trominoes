/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrichromaticGraphOrientationUnaryEncoding
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Reinterpreting compiled fields as native unary graph records -/
noncomputable section
namespace LeanTrominoes.TrichromaticGraphOrientation.UnaryEncoding
open Turing

def encodingCompiler {Source Symbol : Type} {encodeSource : Source → List Symbol} {graph : Source → Input}
    (fields : TM2ComputableInPolyTime encodeSource UnaryFieldEncoderMachine.unaryFields
      (fun s => FlatEncoding.fields (graph s))) :
    TM2ComputableInPolyTime encodeSource finEncoding.encode graph := by
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq fields
  intro s
  rfl

end LeanTrominoes.TrichromaticGraphOrientation.UnaryEncoding
end
