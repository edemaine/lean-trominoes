/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicDrawingFiniteCheck
import LeanTrominoes.BoundedArithmeticSignedGeometry
import LeanTrominoes.PeriodicStripFlatEncoding

/-! # Flat geometry fields and compiled segment access -/
namespace LeanTrominoes.PeriodicGridDrawing.Arithmetic
open BoundedArithmetic BoundedArithmetic.Expr BoundedArithmetic.SignedGeometry

def segmentFields (s : IndexedGridSegment) : List Nat :=
  [s.routeIndex,s.segmentIndex,Encodable.encode s.segment.start.1,Encodable.encode s.segment.start.2,
    Encodable.encode s.segment.finish.1,Encodable.encode s.segment.finish.2]
def pointFields (p : Cell) : List Nat := [Encodable.encode p.1,Encodable.encode p.2]
def routeFields (ps : List Cell) : List Nat := ps.length :: ps.flatMap pointFields
def trailer (d : PeriodicGridDrawing) : List Nat := d.edgeRoutes.length :: d.edgeRoutes.flatMap routeFields

def fields (d : PeriodicGridDrawing) : List Nat :=
  [d.gridSize,FiniteBounds.radius d,d.indexedSegments.length,d.vertexPositions.length] ++
    d.indexedSegments.flatMap segmentFields ++ (d.vertexPositions.flatMap pointFields ++ trailer d)

private theorem segment_get (ss : List IndexedGridSegment) (suffix : List Nat)
    (i : Nat) (axis : Fin 6) (hi : i < ss.length) :
    ((ss.flatMap segmentFields ++ suffix)[6*i+axis.val]?.getD 0) = (segmentFields ss[i])[axis.val]?.getD 0 := by
  induction ss generalizing i with
  | nil => simp at hi
  | cons s ss ih =>
    cases i with
    | zero => fin_cases axis <;> simp [segmentFields]
    | succ i =>
      have h := ih i (by simpa using hi)
      have address : 6*(i+1)+axis.val = (6*i+axis.val)+1+1+1+1+1+1 := by omega
      simpa [segmentFields,address] using h

private theorem point_get (ps : List Cell) (suffix : List Nat) (i : Nat) (axis : Fin 2) (hi : i < ps.length) :
    ((ps.flatMap pointFields ++ suffix)[2*i+axis.val]?.getD 0) = (pointFields ps[i])[axis.val]?.getD 0 := by
  induction ps generalizing i with
  | nil => simp at hi
  | cons p ps ih =>
    cases i with
    | zero => fin_cases axis <;> simp [pointFields]
    | succ i =>
      have h := ih i (by simpa using hi)
      have address : 2*(i+1)+axis.val = (2*i+axis.val)+1+1 := by omega
      simpa [pointFields,address] using h

theorem header_get (d : PeriodicGridDrawing) (front : List Nat) (i : Nat) (hi : i<4) :
    ((front ++ fields d)[front.length+i]?.getD 0) =
      ([d.gridSize,FiniteBounds.radius d,d.indexedSegments.length,d.vertexPositions.length][i]?.getD 0) := by
  rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
  unfold fields
  rw [List.getElem?_append_left (by simp; omega),List.getElem?_append_left (by simpa using hi)]

theorem segment_field (d : PeriodicGridDrawing) (front : List Nat)
    (i : Nat) (axis : Fin 6) (hi : i<d.indexedSegments.length) :
    ((front ++ fields d)[front.length+4+6*i+axis.val]?.getD 0) =
      (segmentFields d.indexedSegments[i])[axis.val]?.getD 0 := by
  rw [List.getElem?_append_right (by omega)]
  have address : front.length+4+6*i+axis.val-front.length = (6*i+axis.val)+1+1+1+1 := by omega
  rw [address]
  simpa [fields,List.append_assoc] using segment_get d.indexedSegments
    (d.vertexPositions.flatMap pointFields ++ trailer d) i axis hi

theorem segmentFields_length (ss : List IndexedGridSegment) : (ss.flatMap segmentFields).length=6*ss.length := by
  induction ss with
  | nil => rfl
  | cons s ss ih => simp [segmentFields,ih]; omega

theorem point_field (d : PeriodicGridDrawing) (front : List Nat)
    (i : Nat) (axis : Fin 2) (hi : i<d.vertexPositions.length) :
    ((front ++ fields d)[front.length+4+6*d.indexedSegments.length+2*i+axis.val]?.getD 0) =
      (pointFields d.vertexPositions[i])[axis.val]?.getD 0 := by
  rw [List.getElem?_append_right (by omega)]
  have address : front.length+4+6*d.indexedSegments.length+2*i+axis.val-front.length =
      (6*d.indexedSegments.length+2*i+axis.val)+1+1+1+1 := by omega
  rw [address]
  simp only [fields,List.append_assoc,List.cons_append,List.nil_append,List.getElem?_cons_succ]
  rw [List.getElem?_append_right (by rw [segmentFields_length]; omega),segmentFields_length]
  have address' : 6*d.indexedSegments.length+2*i+axis.val-6*d.indexedSegments.length = 2*i+axis.val := by omega
  rw [address']
  exact point_get _ (trailer d) i axis hi

def segmentField (depth : Nat) (i : Expr) (axis : Nat) : Expr :=
  .load (.literal (depth+4)+6*i+.literal axis)
def vertexField (depth : Nat) (i : Expr) (axis : Nat) : Expr :=
  .load (.literal (depth+4)+6*var (depth+2)+2*i+.literal axis)
def segment (depth : Nat) (i : Expr) : Segment :=
  ⟨(fromCode (segmentField depth i 2),fromCode (segmentField depth i 3)),
    (fromCode (segmentField depth i 4),fromCode (segmentField depth i 5))⟩
def vertex (depth : Nat) (i : Expr) : Point :=
  (fromCode (vertexField depth i 0),fromCode (vertexField depth i 1))

theorem segmentField_eval (d : PeriodicGridDrawing) (front : List Nat) (index : Expr)
    (i : Nat) (axis : Fin 6) (he : index.eval (front++fields d)=i) (hi : i<d.indexedSegments.length) :
    (segmentField front.length index axis).eval (front++fields d) =
      (segmentFields d.indexedSegments[i])[axis.val]?.getD 0 := by
  simp only [segmentField,Expr.eval,Op.eval,he]
  exact segment_field d front i axis hi

theorem vertexField_eval (d : PeriodicGridDrawing) (front : List Nat) (index : Expr)
    (i : Nat) (axis : Fin 2) (he : index.eval (front++fields d)=i) (hi : i<d.vertexPositions.length) :
    (vertexField front.length index axis).eval (front++fields d) =
      (pointFields d.vertexPositions[i])[axis.val]?.getD 0 := by
  simp only [vertexField,Expr.eval,var,Op.eval,he,header_get d front 2 (by decide)]
  exact point_field d front i axis hi

end LeanTrominoes.PeriodicGridDrawing.Arithmetic
