/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentRealConvexity
import LeanTrominoes.GridSegmentRealScaling
import LeanTrominoes.OrthogonalPolylineUnitSubdivision

/-! # Trimming room for endpoint templates from a scaled orthogonal segment -/
namespace LeanTrominoes.GridSegment

def trimScaled (segment : GridSegment) (firstCut lastCut : Int) : GridSegment :=
  let direction := (AxisDirection.between segment.start segment.finish).step
  ⟨Cell.add (Cell.scale 32 segment.start) (Cell.scale firstCut direction),
    Cell.add (Cell.scale 32 segment.finish) (Cell.scale (-lastCut) direction)⟩

theorem trimScaled_geometry {segment : GridSegment} (aligned : segment.IsAxisAligned)
    {firstCut lastCut : Int} (firstBound : 0 ≤ firstCut ∧ firstCut ≤ 8) (lastBound : 0 ≤ lastCut ∧ lastCut ≤ 8) :
    (segment.trimScaled firstCut lastCut).IsAxisAligned ∧
      (segment.scale 32).Contains (segment.trimScaled firstCut lastCut).start ∧
      (segment.scale 32).Contains (segment.trimScaled firstCut lastCut).finish := by
  have genuine := AxisDirection.between_isGenuine_of_axisAligned aligned
  cases direction : AxisDirection.between segment.start segment.finish with
  | invalid => simp [direction,AxisDirection.IsGenuine] at genuine
  | east =>
    have coords := (AxisDirection.between_eq_east_iff _ _).mp direction
    simp_all [trimScaled,scale,Cell.scale,Cell.add,AxisDirection.step,IsAxisAligned,IsHorizontal,IsVertical,Contains,Between]
    omega
  | north =>
    have coords := (AxisDirection.between_eq_north_iff _ _).mp direction
    simp_all [trimScaled,scale,Cell.scale,Cell.add,AxisDirection.step,IsAxisAligned,IsHorizontal,IsVertical,Contains,Between]
    omega
  | west =>
    have coords := (AxisDirection.between_eq_west_iff _ _).mp direction
    simp_all [trimScaled,scale,Cell.scale,Cell.add,AxisDirection.step,IsAxisAligned,IsHorizontal,IsVertical,Contains,Between]
    omega
  | south =>
    have coords := (AxisDirection.between_eq_south_iff _ _).mp direction
    simp_all [trimScaled,scale,Cell.scale,Cell.add,AxisDirection.step,IsAxisAligned,IsHorizontal,IsVertical,Contains,Between]
    omega

theorem trimScaled_realContains_parent {segment : GridSegment} (aligned : segment.IsAxisAligned)
    {firstCut lastCut : Int} (firstBound : 0 ≤ firstCut ∧ firstCut ≤ 8) (lastBound : 0 ≤ lastCut ∧ lastCut ≤ 8)
    {point : ℝ × ℝ} (contains : (segment.trimScaled firstCut lastCut).RealContains point) :
    (segment.scale 32).RealContains point := by
  have geometry := trimScaled_geometry aligned firstBound lastBound
  exact realContains_of_endpoints_contained (realContains_of_contains geometry.2.1)
    (realContains_of_contains geometry.2.2) contains

theorem trimScaled_avoids_start {segment : GridSegment} (aligned : segment.IsAxisAligned)
    {firstCut lastCut : Int} (firstBound : 0 < firstCut ∧ firstCut ≤ 8) (lastBound : 0 ≤ lastCut ∧ lastCut ≤ 8) :
    ¬ (segment.trimScaled firstCut lastCut).RealContains (realCell (Cell.scale 32 segment.start)) := by
  intro contains
  have geometry := trimScaled_geometry aligned ⟨firstBound.1.le,firstBound.2⟩ lastBound
  have integerContains := contains_of_realBoxContains_of_isAxisAligned geometry.1
    (realBoxContains_of_realContains contains)
  have genuine := AxisDirection.between_isGenuine_of_axisAligned aligned
  cases direction : AxisDirection.between segment.start segment.finish with
  | invalid => simp [direction,AxisDirection.IsGenuine] at genuine
  | east =>
    have coords := (AxisDirection.between_eq_east_iff _ _).mp direction
    simp_all [trimScaled,scale,Cell.scale,Cell.add,AxisDirection.step,IsAxisAligned,IsHorizontal,IsVertical,Contains,Between]
    omega
  | north =>
    have coords := (AxisDirection.between_eq_north_iff _ _).mp direction
    simp_all [trimScaled,scale,Cell.scale,Cell.add,AxisDirection.step,IsAxisAligned,IsHorizontal,IsVertical,Contains,Between]
    omega
  | west =>
    have coords := (AxisDirection.between_eq_west_iff _ _).mp direction
    simp_all [trimScaled,scale,Cell.scale,Cell.add,AxisDirection.step,IsAxisAligned,IsHorizontal,IsVertical,Contains,Between]
    omega
  | south =>
    have coords := (AxisDirection.between_eq_south_iff _ _).mp direction
    simp_all [trimScaled,scale,Cell.scale,Cell.add,AxisDirection.step,IsAxisAligned,IsHorizontal,IsVertical,Contains,Between]
    omega

end LeanTrominoes.GridSegment
