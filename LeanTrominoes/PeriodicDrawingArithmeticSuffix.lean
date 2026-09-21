/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicDrawingArithmeticGeometry
import LeanTrominoes.PeriodicDrawingArithmeticRouteCount

/-! # Drawing accessors with an arbitrary trailing component -/
namespace LeanTrominoes.PeriodicGridDrawing.Arithmetic
open BoundedArithmetic BoundedArithmetic.Expr BoundedArithmetic.SignedGeometry

theorem fields_length_lower (d : PeriodicGridDrawing) :
    4+6*d.indexedSegments.length+2*d.vertexPositions.length ≤ (fields d).length := by
  simp only [fields,List.length_append,List.length_cons,List.length_nil,
    segmentFields_length,pointFields_length]
  omega

theorem header_get_suffix (d : PeriodicGridDrawing) (front rest : List Nat)
    (i : Nat) (hi : i<4) :
    ((front++fields d++rest)[front.length+i]?.getD 0) =
      ([d.gridSize,FiniteBounds.radius d,d.indexedSegments.length,d.vertexPositions.length][i]?.getD 0) := by
  rw [List.getElem?_append_left (by have := fields_length_lower d; simp only [List.length_append]; omega)]
  exact header_get d front i hi

theorem point_field_suffix (d : PeriodicGridDrawing) (front rest : List Nat)
    (i : Nat) (axis : Fin 2) (hi : i<d.vertexPositions.length) :
    ((front++fields d++rest)[front.length+4+6*d.indexedSegments.length+2*i+axis.val]?.getD 0) =
      (pointFields d.vertexPositions[i])[axis.val]?.getD 0 := by
  rw [List.getElem?_append_left (by have := fields_length_lower d; have := axis.isLt; simp only [List.length_append]; omega)]
  exact point_field d front i axis hi

theorem vertexField_eval_suffix (d : PeriodicGridDrawing) (front rest : List Nat) (index : Expr)
    (i : Nat) (axis : Fin 2) (he : index.eval (front++fields d++rest)=i) (hi : i<d.vertexPositions.length) :
    (vertexField front.length index axis).eval (front++fields d++rest) =
      (pointFields d.vertexPositions[i])[axis.val]?.getD 0 := by
  simp only [vertexField,Expr.eval,var,Op.eval,he,header_get_suffix d front rest 2 (by decide)]
  exact point_field_suffix d front rest i axis hi

theorem vertex_eval_suffix (d : PeriodicGridDrawing) (front rest : List Nat) (index : Expr)
    (i : Nat) (he : index.eval (front++fields d++rest)=i) (hi : i<d.vertexPositions.length) :
    pointEval (vertex front.length index) (front++fields d++rest) = d.vertexPositions[i] := by
  have x := fromCode_eval (vertexField front.length index 0) (front++fields d++rest)
    d.vertexPositions[i].1 (by simpa [pointFields] using vertexField_eval_suffix d front rest index i ⟨0,by decide⟩ he hi)
  have y := fromCode_eval (vertexField front.length index 1) (front++fields d++rest)
    d.vertexPositions[i].2 (by simpa [pointFields] using vertexField_eval_suffix d front rest index i ⟨1,by decide⟩ he hi)
  simp only [vertex,pointEval,x,y]

end LeanTrominoes.PeriodicGridDrawing.Arithmetic
