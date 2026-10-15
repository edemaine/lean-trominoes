/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentKickedDigitalRouteBounds
import LeanTrominoes.Common.Geometry.GridSegmentOrderedCoreDigitalRoutes

/-! # Separation estimates for digital cores with endpoint steps

Endpoint steps increase the digital tube radius from two to three. The
required refinement factors remain linear in the original direction and
slope bounds. Exterior-half-plane contacts isolate the two endpoint fans.
-/
namespace LeanTrominoes.GridSegment

theorem BoundedEndpointPerturbation.kickedDigitalRoute_tube {radius firstFactor secondFactor side : Int}
    {original output : GridSegment}
    (perturbed : BoundedEndpointPerturbation radius firstFactor original output)
    (positive : 0 < secondFactor) (unit : side = 1 ∨ side = -1) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains ((output.scale secondFactor).kickedDigitalRoute side) point) :
    (original.scale (secondFactor*firstFactor)).RealTubeContains ((secondFactor : ℝ)*radius+3) point :=
  ((output.scale secondFactor).kickedDigitalRoute_tube
    (by rcases unit with rfl | rfl <;> norm_num)
    (by rcases unit with rfl | rfl <;> norm_num) contains).compose
      (fun _ contains => perturbed.scaled_tube positive contains)

theorem bounded_core_kickedDigitalRoutes_disjoint {bound radius firstFactor secondFactor firstSide secondSide : Int}
    (boundPositive : 1 ≤ bound) (radiusNonnegative : 0 ≤ radius) (secondPositive : 0 < secondFactor)
    (firstUnit : firstSide = 1 ∨ firstSide = -1) (secondUnit : secondSide = 1 ∨ secondSide = -1)
    (spacing : 4*bound*(radius+3) < firstFactor) {first second firstCore secondCore : GridSegment}
    (firstBounds : |first.direction.1| ≤ bound ∧ |first.direction.2| ≤ bound)
    (secondBounds : |second.direction.1| ≤ bound ∧ |second.direction.2| ≤ bound)
    (firstPerturbed : BoundedEndpointPerturbation radius firstFactor first firstCore)
    (secondPerturbed : BoundedEndpointPerturbation radius firstFactor second secondCore)
    (disjoint : ∀ point : ℝ × ℝ, first.RealContains point → ¬second.RealContains point)
    {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains ((firstCore.scale secondFactor).kickedDigitalRoute firstSide) point) :
    ¬GridPolyline.RealContains ((secondCore.scale secondFactor).kickedDigitalRoute secondSide) point := by
  intro secondContains
  have firstTube := firstPerturbed.kickedDigitalRoute_tube secondPositive firstUnit firstContains
  have secondTube := secondPerturbed.kickedDigitalRoute_tube secondPositive secondUnit secondContains
  have tubeRadiusNonnegative : (0 : ℝ) ≤ (secondFactor : ℝ)*radius+3 := by positivity
  have tubeSpacing : 4*(bound : ℝ)*((secondFactor : ℝ)*radius+3) < (secondFactor*firstFactor : Int) := by
    have secondAtLeastOne : (1 : ℝ) ≤ secondFactor := by exact_mod_cast (show 1 ≤ secondFactor by omega)
    have boundNonnegative : (0 : ℝ) ≤ bound := by exact_mod_cast (show 0 ≤ bound by omega)
    have realSpacing : 4*(bound : ℝ)*((radius : ℝ)+3) < firstFactor := by exact_mod_cast spacing
    have scaledSpacing := mul_lt_mul_of_pos_left realSpacing
      (by exact_mod_cast secondPositive : (0 : ℝ) < secondFactor)
    push_cast
    nlinarith [mul_nonneg boundNonnegative (sub_nonneg.mpr secondAtLeastOne)]
  exact scaled_tubes_disjoint boundPositive tubeRadiusNonnegative tubeSpacing
    firstBounds secondBounds disjoint point firstTube secondTube

theorem ordered_right_kickedDigitalRoutes_disjoint {first second : GridSegment} {bound factor : Int}
    (boundNonnegative : 0 ≤ bound) (factorPositive : 0 < factor)
    (firstPositive : 0 < first.direction.1) (secondPositive : 0 < second.direction.1)
    (sameColumn : first.start.1 = second.start.1) (ports : first.start.2+2 ≤ second.start.2)
    (ordered : 0 ≤ cross first.direction second.direction) (slopeBound : |second.realSlope| ≤ bound)
    (spacing : 3*(bound+1) < factor) {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains ((first.scale factor).kickedDigitalRoute 1) point) :
    ¬GridPolyline.RealContains ((second.scale factor).kickedDigitalRoute 1) point := by
  intro secondContains
  have firstHorizontal : 0 < (first.scale factor).direction.1 := by
    simp only [direction_scale,Cell.scale]
    exact mul_pos factorPositive firstPositive
  have secondHorizontal : 0 < (second.scale factor).direction.1 := by
    simp only [direction_scale,Cell.scale]
    exact mul_pos factorPositive secondPositive
  have scaledColumn : (first.scale factor).start.1 = (second.scale factor).start.1 := by
    simp only [scale,Cell.scale,sameColumn]
  have scaledPorts : ((first.scale factor).start.2 : ℝ)+2*(factor : ℝ) ≤ (second.scale factor).start.2 := by
    have scaled := mul_le_mul_of_nonneg_left ports factorPositive.le
    have scaled' : factor*first.start.2+2*factor ≤ factor*second.start.2 := by nlinarith
    simp only [scale,Cell.scale,Int.cast_mul]
    exact_mod_cast scaled'
  have scaledOrder : 0 ≤ cross (first.scale factor).direction (second.scale factor).direction := by
    rw [cross_scaled_directions]
    exact mul_nonneg (by positivity) ordered
  have scaledSlope : |(second.scale factor).realSlope| ≤ (bound : ℝ) := by
    rw [realSlope_scale second (ne_of_gt factorPositive)]
    exact slopeBound
  have realSpacing : 2*(3 : ℝ)*((bound : ℝ)+1) < 2*(factor : ℝ) := by
    have castSpacing : 3*((bound : ℝ)+1) < factor := by exact_mod_cast spacing
    linarith
  exact ordered_right_tubes_disjoint (by exact_mod_cast boundNonnegative) firstHorizontal secondHorizontal
    scaledColumn scaledPorts scaledOrder scaledSlope realSpacing
    ((first.scale factor).kickedDigitalRoute_tube (by norm_num) (by norm_num) firstContains)
    ((second.scale factor).kickedDigitalRoute_tube (by norm_num) (by norm_num) secondContains)

theorem kickedDigitalRoute_source_fan_contacts {segment : GridSegment} {side : Int} {fan : List Cell}
    (unit : side = 1 ∨ side = -1) (wide : 3 ≤ side*(segment.finish.1-segment.start.1))
    (fanSide : ∀ point, GridPolyline.RealContains fan point → (side : ℝ)*(point.1-segment.start.1) ≤ 0)
    {point : ℝ × ℝ} (coreContains : GridPolyline.RealContains (segment.kickedDigitalRoute side) point)
    (fanContains : GridPolyline.RealContains fan point) : point = realCell segment.start :=
  (kickedDigitalRoute_exterior_contacts unit wide coreContains).1 (fanSide point fanContains)

theorem kickedDigitalRoute_target_fan_contacts {segment : GridSegment} {side : Int} {fan : List Cell}
    (unit : side = 1 ∨ side = -1) (wide : 3 ≤ side*(segment.finish.1-segment.start.1))
    (fanSide : ∀ point, GridPolyline.RealContains fan point → (side : ℝ)*((segment.finish.1 : ℝ)-point.1) ≤ 0)
    {point : ℝ × ℝ} (coreContains : GridPolyline.RealContains (segment.kickedDigitalRoute side) point)
    (fanContains : GridPolyline.RealContains fan point) : point = realCell segment.finish :=
  (kickedDigitalRoute_exterior_contacts unit wide coreContains).2 (fanSide point fanContains)

end LeanTrominoes.GridSegment
