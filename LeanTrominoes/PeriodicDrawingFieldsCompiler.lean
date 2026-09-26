/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicDrawingHeaderCompiler

/-! # Complete native drawing-field assembly from its three tables -/
noncomputable section
namespace LeanTrominoes.PeriodicGridDrawing.NativeCompiler
open Computability Turing UnaryColumn
open UnaryFieldEncoderMachine (unaryFields)
variable {Symbol : Type} [Fintype Symbol] [Inhabited Symbol]

def fieldsCompiler (drawing : List Symbol → PeriodicGridDrawing)
    (size : ScalarCompiler (fun s => (drawing s).gridSize))
    (segments : TM2ComputableInPolyTime id unaryFields
      (fun s => (drawing s).indexedSegments.flatMap Arithmetic.segmentFields))
    (vertices : TM2ComputableInPolyTime id unaryFields
      (fun s => (drawing s).vertexPositions.flatMap Arithmetic.pointFields))
    (routes : TM2ComputableInPolyTime id unaryFields (fun s => Arithmetic.trailer (drawing s))) :
    TM2ComputableInPolyTime id unaryFields (fun s => Arithmetic.fields (drawing s)) := by
  let headers := UnaryFieldClosure.appendCompiler id _ _ size
    (UnaryFieldClosure.appendCompiler id _ _ (radiusCompiler drawing vertices segments)
      (UnaryFieldClosure.appendCompiler id _ _
        (UnarySegmentFieldsProjection.countCompiler (fun s => (drawing s).indexedSegments) segments)
        (vertexCountCompiler drawing vertices)))
  let body := UnaryFieldClosure.appendCompiler id _ _ segments
    (UnaryFieldClosure.appendCompiler id _ _ vertices routes)
  let physical := UnaryFieldClosure.appendCompiler id _ _ headers body
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  simp only [Arithmetic.fields, List.cons_append, List.nil_append]

end LeanTrominoes.PeriodicGridDrawing.NativeCompiler
end
