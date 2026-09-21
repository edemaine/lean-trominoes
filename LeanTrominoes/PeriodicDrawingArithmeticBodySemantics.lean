/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicDrawingArithmeticPredicate

/-! # Meaning of the drawing checker's innermost tests -/
namespace LeanTrominoes.PeriodicGridDrawing.Arithmetic
open BoundedArithmetic BoundedArithmetic.Expr BoundedArithmetic.SignedGeometry

def relative (d : PeriodicGridDrawing) (x y : Nat) : Cell :=
  ((x:Int)-2*(FiniteBounds.radius d:Int),(y:Int)-2*(FiniteBounds.radius d:Int))
def point (d : PeriodicGridDrawing) (x y : Nat) : Cell :=
  ((x:Int)-(FiniteBounds.radius d:Int),(y:Int)-(FiniteBounds.radius d:Int))

theorem routeBody_truth (d : PeriodicGridDrawing) (a b x y px py : Nat)
    (ha : a<d.indexedSegments.length) (hb : b<d.indexedSegments.length) :
    routeBody.Truth ([py,px,y,x,b,a]++fields d) ↔
      SegmentOccurrenceKey d.indexedSegments[a] (relative d x y) = SegmentOccurrenceKey d.indexedSegments[b] (0,0) ∨
        ¬ ((d.indexedSegments[a].segment.translate (d.periodTranslation (relative d x y))).InteriorContains (point d px py) ∧
          d.indexedSegments[b].segment.Contains (point d px py)) := by
  let front := [py,px,y,x,b,a]
  rw [routeBody,truth_or,truth_not,truth_and,interiorContains_truth,contains_truth]
  have key := sameKey_truth d front (var 5) (var 4) (var 3) (var 2) a b rfl rfl ha hb
  have first := translateSegment_eval d front (var 5) (var 3) (var 2) a rfl ha
  have second := segment_eval d front (var 4) b rfl hb
  have pt := probe_eval d front (var 1) (var 0)
  simp only [front,List.length_cons,List.length_nil,Nat.reduceAdd] at key first second pt
  rw [key,first,second,pt]
  rfl

theorem continuousBody_truth (d : PeriodicGridDrawing) (a b x y : Nat)
    (ha : a<d.indexedSegments.length) (hb : b<d.indexedSegments.length) :
    continuousBody.Truth ([y,x,b,a]++fields d) ↔
      SegmentOccurrenceKey d.indexedSegments[a] (relative d x y) = SegmentOccurrenceKey d.indexedSegments[b] (0,0) ∨
        ¬ GridSegment.InteriorsMeet
          (d.indexedSegments[a].segment.translate (d.periodTranslation (relative d x y))) d.indexedSegments[b].segment := by
  let front := [y,x,b,a]
  rw [continuousBody,truth_or,truth_not,interiorsMeet_truth]
  have key := sameKey_truth d front (var 3) (var 2) (var 1) (var 0) a b rfl rfl ha hb
  have first := translateSegment_eval d front (var 3) (var 1) (var 0) a rfl ha
  have second := segment_eval d front (var 2) b rfl hb
  simp only [front,List.length_cons,List.length_nil,Nat.reduceAdd] at key first second
  rw [key,first,second]
  rfl

theorem vertexBody_truth (d : PeriodicGridDrawing) (v a x y : Nat)
    (hv : v<d.vertexPositions.length) (ha : a<d.indexedSegments.length) :
    vertexBody.Truth ([y,x,a,v]++fields d) ↔
      ¬ (d.indexedSegments[a].segment.translate (d.periodTranslation (relative d x y))).InteriorContains d.vertexPositions[v] := by
  let front := [y,x,a,v]
  rw [vertexBody,truth_not,interiorContains_truth]
  have first := translateSegment_eval d front (var 2) (var 1) (var 0) a rfl ha
  have pt := vertex_eval d front (var 3) v rfl hv
  simp only [front,List.length_cons,List.length_nil,Nat.reduceAdd] at first pt
  rw [first,pt]
  rfl

end LeanTrominoes.PeriodicGridDrawing.Arithmetic
