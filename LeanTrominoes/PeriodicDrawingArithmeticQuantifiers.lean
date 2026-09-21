/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicDrawingArithmeticBodySemantics

/-! # Bounded quantifier semantics of the drawing checker -/
namespace LeanTrominoes.PeriodicGridDrawing.Arithmetic
open BoundedArithmetic BoundedArithmetic.Expr

def RoutesBounded (d : PeriodicGridDrawing) : Prop :=
  ∀ a (ha : a<d.indexedSegments.length) b (hb : b<d.indexedSegments.length),
    ∀ x<4*FiniteBounds.radius d+1, ∀ y<4*FiniteBounds.radius d+1,
      ∀ px<2*FiniteBounds.radius d+1, ∀ py<2*FiniteBounds.radius d+1,
        SegmentOccurrenceKey d.indexedSegments[a] (relative d x y) = SegmentOccurrenceKey d.indexedSegments[b] (0,0) ∨
          ¬ ((d.indexedSegments[a].segment.translate (d.periodTranslation (relative d x y))).InteriorContains (point d px py) ∧
            d.indexedSegments[b].segment.Contains (point d px py))

def VerticesBounded (d : PeriodicGridDrawing) : Prop :=
  ∀ v (hv : v<d.vertexPositions.length) a (ha : a<d.indexedSegments.length),
    ∀ x<4*FiniteBounds.radius d+1, ∀ y<4*FiniteBounds.radius d+1,
      ¬ (d.indexedSegments[a].segment.translate (d.periodTranslation (relative d x y))).InteriorContains d.vertexPositions[v]

def ContinuousBounded (d : PeriodicGridDrawing) : Prop :=
  ∀ a (ha : a<d.indexedSegments.length) b (hb : b<d.indexedSegments.length),
    ∀ x<4*FiniteBounds.radius d+1, ∀ y<4*FiniteBounds.radius d+1,
      SegmentOccurrenceKey d.indexedSegments[a] (relative d x y) = SegmentOccurrenceKey d.indexedSegments[b] (0,0) ∨
        ¬ GridSegment.InteriorsMeet
          (d.indexedSegments[a].segment.translate (d.periodTranslation (relative d x y))) d.indexedSegments[b].segment

theorem routePredicate_truth (d : PeriodicGridDrawing) : routePredicate.Truth (fields d) ↔ RoutesBounded d := by
  simp only [routePredicate,truth_all]
  change (∀ a<d.indexedSegments.length, ∀ b<d.indexedSegments.length,
    ∀ x<4*FiniteBounds.radius d+1, ∀ y<4*FiniteBounds.radius d+1,
      ∀ px<2*FiniteBounds.radius d+1, ∀ py<2*FiniteBounds.radius d+1,
        routeBody.Truth ([py,px,y,x,b,a]++fields d)) ↔ _
  unfold RoutesBounded
  refine forall_congr' fun a => forall_congr' fun ha => forall_congr' fun b => forall_congr' fun hb => ?_
  simp only [routeBody_truth d a b _ _ _ _ ha hb]

theorem vertexPredicate_truth (d : PeriodicGridDrawing) : vertexPredicate.Truth (fields d) ↔ VerticesBounded d := by
  simp only [vertexPredicate,truth_all]
  change (∀ v<d.vertexPositions.length, ∀ a<d.indexedSegments.length,
    ∀ x<4*FiniteBounds.radius d+1, ∀ y<4*FiniteBounds.radius d+1,
      vertexBody.Truth ([y,x,a,v]++fields d)) ↔ _
  unfold VerticesBounded
  refine forall_congr' fun v => forall_congr' fun hv => forall_congr' fun a => forall_congr' fun ha => ?_
  simp only [vertexBody_truth d v a _ _ hv ha]

theorem continuousPredicate_truth (d : PeriodicGridDrawing) : continuousPredicate.Truth (fields d) ↔ ContinuousBounded d := by
  simp only [continuousPredicate,truth_all]
  change (∀ a<d.indexedSegments.length, ∀ b<d.indexedSegments.length,
    ∀ x<4*FiniteBounds.radius d+1, ∀ y<4*FiniteBounds.radius d+1,
      continuousBody.Truth ([y,x,b,a]++fields d)) ↔ _
  unfold ContinuousBounded
  refine forall_congr' fun a => forall_congr' fun ha => forall_congr' fun b => forall_congr' fun hb => ?_
  simp only [continuousBody_truth d a b _ _ ha hb]

end LeanTrominoes.PeriodicGridDrawing.Arithmetic
