/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Orientation.TrichromaticGraphOrientationFlatEncoding
import LeanTrominoes.Computation.Encoding.Unary.UnaryColumnSignedEncoding
import LeanTrominoes.Computation.Encoding.Unary.UnaryFieldClosure

/-! # Assembling the native graph header and tables -/
noncomputable section
namespace LeanTrominoes.TrichromaticGraphOrientation.FlatEncoding
open Turing UnaryColumn
variable {Symbol : Type} [Fintype Symbol] [Inhabited Symbol] {graph : List Symbol → Input}

def fieldsCompiler
    (vertices : ScalarCompiler (fun s => (graph s).1.length))
    (edges : ScalarCompiler (fun s => (graph s).2.length))
    (kinds : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun s => (graph s).1.map Bool.toNat))
    (body : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun s => (graph s).2.flatMap edgeFields)) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields (fun s => fields (graph s)) := by
  let physical := UnaryFieldClosure.appendCompiler id _ _ vertices
    (UnaryFieldClosure.appendCompiler id _ _ edges (UnaryFieldClosure.appendCompiler id _ _ kinds body))
  exact TM2ComputableInPolyTime.of_eq physical (fun _ => rfl)

def encodingCompiler
    (compiler : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields (fun s => fields (graph s))) :
    TM2ComputableInPolyTime id finEncoding.encode graph := by
  let physical := TM2CompositionMachine.computableInPolyTime compiler UnaryFieldEncoderMachine.computableInPolyTime
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical
  intro s
  exact (PeriodicCNFFlatEncoding.encodeNatFields_eq_trList (fields (graph s))).symm

end LeanTrominoes.TrichromaticGraphOrientation.FlatEncoding
end
