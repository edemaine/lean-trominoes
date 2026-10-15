/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentRealConvexity
import LeanTrominoes.Graphs.Drawings.Orthogonal.OrthogonalPolylineUnitSubdivision
import LeanTrominoes.Graphs.Drawings.Orthogonal.OrthogonalPolylineEndpointDirections

/-! # A half-unit point on every genuine orthogonal endpoint ray -/
namespace LeanTrominoes

noncomputable def realHalfStep (start : Cell) (direction : AxisDirection) : ℝ × ℝ :=
  ((start.1 : ℝ)+(direction.step.1 : ℝ)/2,(start.2 : ℝ)+(direction.step.2 : ℝ)/2)

theorem realHalfStep_not_integral (start : Cell) {direction : AxisDirection} (genuine : direction.IsGenuine)
    (point : Cell) : realHalfStep start direction ≠ realCell point := by
  intro equal
  cases direction with
  | invalid => simp [AxisDirection.IsGenuine] at genuine
  | east =>
    have hx := congrArg Prod.fst equal
    simp [realHalfStep,realCell,AxisDirection.step] at hx
    have odd : 2*(point.1-start.1) = 1 := by exact_mod_cast (by linarith : (2 : ℝ)*((point.1 : ℝ)-start.1) = 1)
    omega
  | north =>
    have hy := congrArg Prod.snd equal
    simp [realHalfStep,realCell,AxisDirection.step] at hy
    have odd : 2*(point.2-start.2) = 1 := by exact_mod_cast (by linarith : (2 : ℝ)*((point.2 : ℝ)-start.2) = 1)
    omega
  | west =>
    have hx := congrArg Prod.fst equal
    simp [realHalfStep,realCell,AxisDirection.step] at hx
    have odd : 2*(point.1-start.1) = -1 := by exact_mod_cast (by linarith : (2 : ℝ)*((point.1 : ℝ)-start.1) = -1)
    omega
  | south =>
    have hy := congrArg Prod.snd equal
    simp [realHalfStep,realCell,AxisDirection.step] at hy
    have odd : 2*(point.2-start.2) = -1 := by exact_mod_cast (by linarith : (2 : ℝ)*((point.2 : ℝ)-start.2) = -1)
    omega

theorem GridSegment.realContains_halfStep {segment : GridSegment} (aligned : segment.IsAxisAligned) :
    segment.RealContains (realHalfStep segment.start (AxisDirection.between segment.start segment.finish)) := by
  let length := AxisDirection.segmentLength segment.start segment.finish
  let direction := AxisDirection.between segment.start segment.finish
  have positive : 0 < length := AxisDirection.segmentLength_positive_of_axisAligned aligned
  have lengthPositive : (0 : ℝ) < length := by exact_mod_cast positive
  have lengthBound : (1 : ℝ) ≤ length := by exact_mod_cast (by omega : 1 ≤ length)
  have endpoint := AxisDirection.add_length_step_eq_second_of_axisAligned aligned
  have vx := congrArg Prod.fst endpoint
  have vy := congrArg Prod.snd endpoint
  have dx : (segment.finish.1 : ℝ)-segment.start.1 = (length : ℝ)*direction.step.1 := by
    have cast : (segment.start.1 : ℝ)+(length : ℝ)*direction.step.1 = segment.finish.1 := by
      exact_mod_cast vx
    linarith
  have dy : (segment.finish.2 : ℝ)-segment.start.2 = (length : ℝ)*direction.step.2 := by
    have cast : (segment.start.2 : ℝ)+(length : ℝ)*direction.step.2 = segment.finish.2 := by
      exact_mod_cast vy
    linarith
  refine ⟨1/(2*(length : ℝ)),by positivity,?_,?_,?_⟩
  · apply (div_le_one (by positivity : (0 : ℝ) < 2*length)).mpr
    linarith
  · change (segment.start.1 : ℝ)+(direction.step.1 : ℝ)/2 = _
    rw [dx]
    field_simp <;> ring
  · change (segment.start.2 : ℝ)+(direction.step.2 : ℝ)/2 = _
    rw [dy]
    field_simp <;> ring

theorem GridPolyline.realContains_halfStep_at_head {route : List Cell} {head : Cell}
    (long : 2 ≤ route.length) (orthogonal : PeriodicOrthocrossing.OrthogonalPolyline route)
    (atHead : route.head? = some head) :
    GridPolyline.RealContains route (realHalfStep head (AxisDirection.polylineFirstDirection route)) := by
  cases route with
  | nil => simp at long
  | cons first rest =>
    cases rest with
    | nil => simp at long
    | cons second rest =>
      simp only [List.head?_cons,Option.some.injEq] at atHead
      subst first
      refine ⟨⟨head,second⟩,by simp [gridPolylineSegments],?_⟩
      exact GridSegment.realContains_halfStep (List.isChain_cons_cons.mp orthogonal).1

end LeanTrominoes
