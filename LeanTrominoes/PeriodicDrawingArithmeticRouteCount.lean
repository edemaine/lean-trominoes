/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicDrawingArithmeticFields

/-! # Accessing the route trailer's count in a combined field stream -/
namespace LeanTrominoes.PeriodicGridDrawing.Arithmetic

theorem pointFields_length (points : List Cell) :
    (points.flatMap pointFields).length = 2*points.length := by
  induction points with
  | nil => rfl
  | cons p ps ih => simp [pointFields,ih]; omega

theorem routeCount_field (d : PeriodicGridDrawing) (front rest : List Nat) :
    ((front ++ fields d ++ rest)[front.length+4+6*d.indexedSegments.length+2*d.vertexPositions.length]?.getD 0) =
      d.edgeRoutes.length := by
  rw [List.append_assoc,List.getElem?_append_right (by omega)]
  have offset : front.length+4+6*d.indexedSegments.length+2*d.vertexPositions.length-front.length =
      (6*d.indexedSegments.length+2*d.vertexPositions.length)+1+1+1+1 := by omega
  rw [offset]
  simp only [fields,List.cons_append,List.nil_append,List.append_assoc,List.getElem?_cons_succ]
  rw [List.getElem?_append_right (by rw [segmentFields_length]; omega),segmentFields_length]
  rw [show 6*d.indexedSegments.length+2*d.vertexPositions.length-6*d.indexedSegments.length =
    2*d.vertexPositions.length by omega]
  rw [List.getElem?_append_right (by rw [pointFields_length]),pointFields_length,Nat.sub_self]
  simp [trailer]

end LeanTrominoes.PeriodicGridDrawing.Arithmetic
