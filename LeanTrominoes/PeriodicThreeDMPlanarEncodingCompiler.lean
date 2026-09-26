/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeDMFlatEncoding
import LeanTrominoes.UnaryFieldAggregateCompiler
import LeanTrominoes.UnaryFieldClosure

/-! # Complete native 3DM instance-and-drawing encoding assembly -/
noncomputable section
namespace LeanTrominoes.PeriodicThreeDM.FlatEncoding.Planar
open Turing
open UnaryFieldEncoderMachine (unaryFields)
variable {Symbol : Type} [Fintype Symbol] [Inhabited Symbol]

def fieldsCompiler {input : List Symbol → NormalizationCompiler.Input}
    (problem : TM2ComputableInPolyTime id unaryFields (fun s => FlatEncoding.fields (input s).problem))
    (drawing : TM2ComputableInPolyTime id unaryFields (fun s => PeriodicGridDrawing.Arithmetic.fields (input s).drawing)) :
    TM2ComputableInPolyTime id unaryFields (fun s => fields (input s)) := by
  let count := TM2CompositionMachine.computableInPolyTime drawing UnaryFieldAggregate.countCompiler
  exact UnaryFieldClosure.appendCompiler id _ _ count
    (UnaryFieldClosure.appendCompiler id _ _ drawing problem)

def encodingCompiler {input : List Symbol → NormalizationCompiler.Input}
    (problem : TM2ComputableInPolyTime id unaryFields (fun s => FlatEncoding.fields (input s).problem))
    (drawing : TM2ComputableInPolyTime id unaryFields (fun s => PeriodicGridDrawing.Arithmetic.fields (input s).drawing)) :
    TM2ComputableInPolyTime id finEncoding.encode input := by
  let physical := TM2CompositionMachine.computableInPolyTime (fieldsCompiler problem drawing)
    UnaryFieldEncoderMachine.computableInPolyTime
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical
  intro s
  exact (PeriodicCNFFlatEncoding.encodeNatFields_eq_trList (fields (input s))).symm

end LeanTrominoes.PeriodicThreeDM.FlatEncoding.Planar
end
