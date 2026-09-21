/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicDrawingArithmeticFields

/-! # Typed semantics of the arithmetic drawing accessors -/
namespace LeanTrominoes.PeriodicGridDrawing.Arithmetic
open BoundedArithmetic BoundedArithmetic.Expr BoundedArithmetic.SignedGeometry

theorem segment_eval (d : PeriodicGridDrawing) (front : List Nat) (index : Expr)
    (i : Nat) (he : index.eval (front++fields d)=i) (hi : i<d.indexedSegments.length) :
    (segment front.length index).eval (front++fields d) = d.indexedSegments[i].segment := by
  have x₁ := fromCode_eval (segmentField front.length index 2) (front++fields d)
    d.indexedSegments[i].segment.start.1 (by simpa [segmentFields] using segmentField_eval d front index i ⟨2,by decide⟩ he hi)
  have y₁ := fromCode_eval (segmentField front.length index 3) (front++fields d)
    d.indexedSegments[i].segment.start.2 (by simpa [segmentFields] using segmentField_eval d front index i ⟨3,by decide⟩ he hi)
  have x₂ := fromCode_eval (segmentField front.length index 4) (front++fields d)
    d.indexedSegments[i].segment.finish.1 (by simpa [segmentFields] using segmentField_eval d front index i ⟨4,by decide⟩ he hi)
  have y₂ := fromCode_eval (segmentField front.length index 5) (front++fields d)
    d.indexedSegments[i].segment.finish.2 (by simpa [segmentFields] using segmentField_eval d front index i ⟨5,by decide⟩ he hi)
  simp only [segment,Segment.eval,pointEval,x₁,y₁,x₂,y₂]

theorem vertex_eval (d : PeriodicGridDrawing) (front : List Nat) (index : Expr)
    (i : Nat) (he : index.eval (front++fields d)=i) (hi : i<d.vertexPositions.length) :
    pointEval (vertex front.length index) (front++fields d) = d.vertexPositions[i] := by
  have x := fromCode_eval (vertexField front.length index 0) (front++fields d)
    d.vertexPositions[i].1 (by simpa [pointFields] using vertexField_eval d front index i ⟨0,by decide⟩ he hi)
  have y := fromCode_eval (vertexField front.length index 1) (front++fields d)
    d.vertexPositions[i].2 (by simpa [pointFields] using vertexField_eval d front index i ⟨1,by decide⟩ he hi)
  simp only [vertex,pointEval,x,y]

/-- Two bounded counters give the relative translation in [-2R,2R]². -/
def shift (depth : Nat) (x y : Expr) : Point :=
  (difference x (2*var (depth+1)),difference y (2*var (depth+1)))
def translateSegment (depth : Nat) (i x y : Expr) : Segment :=
  translate (segment depth i) (pointScale (var depth) (shift depth x y))
def probe (depth : Nat) (x y : Expr) : Point :=
  (difference x (var (depth+1)),difference y (var (depth+1)))
def sameKey (depth : Nat) (a b x y : Expr) : Expr :=
  andE (eqE (segmentField depth a 0) (segmentField depth b 0))
    (andE (eqE (segmentField depth a 1) (segmentField depth b 1))
      (andE (eqE x (2*var (depth+1))) (eqE y (2*var (depth+1)))))

theorem header_eval (d : PeriodicGridDrawing) (front : List Nat) (i : Fin 4) :
    (var (front.length+i.val)).eval (front++fields d) =
      ([d.gridSize,FiniteBounds.radius d,d.indexedSegments.length,d.vertexPositions.length][i.val]?.getD 0) :=
  header_get d front i i.isLt

theorem shift_eval (d : PeriodicGridDrawing) (front : List Nat) (x y : Expr) :
    pointEval (shift front.length x y) (front++fields d) =
      ((x.eval (front++fields d):Int)-2*(FiniteBounds.radius d:Int),
        (y.eval (front++fields d):Int)-2*(FiniteBounds.radius d:Int)) := by
  have hr : (var (front.length+1)).eval (front++fields d)=FiniteBounds.radius d := header_eval d front ⟨1,by decide⟩
  simp only [shift,pointEval,difference_eval,eval_mul,hr]
  rfl

theorem probe_eval (d : PeriodicGridDrawing) (front : List Nat) (x y : Expr) :
    pointEval (probe front.length x y) (front++fields d) =
      ((x.eval (front++fields d):Int)-(FiniteBounds.radius d:Int),
        (y.eval (front++fields d):Int)-(FiniteBounds.radius d:Int)) := by
  simp [probe,pointEval,header_eval d front ⟨1,by decide⟩]

theorem translateSegment_eval (d : PeriodicGridDrawing) (front : List Nat) (index x y : Expr)
    (i : Nat) (he : index.eval (front++fields d)=i) (hi : i<d.indexedSegments.length) :
    (translateSegment front.length index x y).eval (front++fields d) =
      d.indexedSegments[i].segment.translate (d.periodTranslation
        ((x.eval (front++fields d):Int)-2*(FiniteBounds.radius d:Int),
          (y.eval (front++fields d):Int)-2*(FiniteBounds.radius d:Int))) := by
  have hp : (var front.length).eval (front++fields d)=d.gridSize := header_eval d front ⟨0,by decide⟩
  simp only [translateSegment,translate_eval,pointScale_eval,segment_eval d front index i he hi,
    shift_eval,hp]
  rfl

theorem sameKey_truth (d : PeriodicGridDrawing) (front : List Nat) (a b x y : Expr)
    (i j : Nat) (ha : a.eval (front++fields d)=i) (hb : b.eval (front++fields d)=j)
    (hi : i<d.indexedSegments.length) (hj : j<d.indexedSegments.length) :
    (sameKey front.length a b x y).Truth (front++fields d) ↔
      SegmentOccurrenceKey d.indexedSegments[i]
        ((x.eval (front++fields d):Int)-2*(FiniteBounds.radius d:Int),
          (y.eval (front++fields d):Int)-2*(FiniteBounds.radius d:Int)) =
        SegmentOccurrenceKey d.indexedSegments[j] (0,0) := by
  simp only [sameKey,truth_and,truth_eq,eval_mul,eval_nat,
    segmentField_eval d front a i ⟨0,by decide⟩ ha hi,
    segmentField_eval d front a i ⟨1,by decide⟩ ha hi,
    segmentField_eval d front b j ⟨0,by decide⟩ hb hj,
    segmentField_eval d front b j ⟨1,by decide⟩ hb hj,
    header_eval d front ⟨1,by decide⟩,segmentFields,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,SegmentOccurrenceKey,Prod.mk.injEq]
  simp only [show (2 : Expr).eval (front++fields d) = 2 from rfl]
  omega

end LeanTrominoes.PeriodicGridDrawing.Arithmetic
