/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentOrderedRayTubes
import LeanTrominoes.GridSegmentBoundedCoreTubes

/-! # Rasterized ordered cores leaving a common side

Constant port spacing and a linear bound on core slopes permit a second
refinement linear in the original grid size. This avoids applying the
integer separating-axis estimate to the much longer perturbed cores.
-/
namespace LeanTrominoes.GridSegment

theorem direction_scale (segment : GridSegment) (factor : Int) :
    (segment.scale factor).direction = Cell.scale factor segment.direction := by
  simp only [direction,scale,Cell.scale]
  apply Prod.ext <;> dsimp <;> ring

theorem realSlope_scale (segment : GridSegment) {factor : Int} (nonzero : factor ≠ 0) :
    (segment.scale factor).realSlope = segment.realSlope := by
  have realNonzero : (factor : ℝ) ≠ 0 := by exact_mod_cast nonzero
  simp only [realSlope,direction_scale,Cell.scale,Int.cast_mul]
  exact mul_div_mul_left _ _ realNonzero

theorem cross_scaled_directions (first second : GridSegment) (factor : Int) :
    cross (first.scale factor).direction (second.scale factor).direction =
      factor*factor*cross first.direction second.direction := by
  simp only [direction_scale,Cell.scale,cross]
  ring

theorem perturbed_right_core_slope {radius factor bound : Int} {original core : GridSegment}
    (perturbed : BoundedEndpointPerturbation radius factor original core)
    (radiusNonnegative : 0 ≤ radius) (boundNonnegative : 0 ≤ bound) (spacing : 4*radius < factor)
    (rightward : 0 < original.direction.1) (verticalBound : |original.direction.2| ≤ bound) :
    0 < core.direction.1 ∧ |core.realSlope| ≤ (2*bound+1 : Int) := by
  have bounds := perturbed.direction.horizontal_slope_bound (by omega) boundNonnegative
    (by omega) rightward verticalBound
  refine ⟨bounds.1,?_⟩
  have positive : (0 : ℝ) < core.direction.1 := by exact_mod_cast bounds.1
  have castBound : |(core.direction.2 : ℝ)| ≤ (2*(bound : ℝ)+1)*core.direction.1 := by
    exact_mod_cast bounds.2
  simp only [realSlope,abs_div,abs_of_pos positive,Int.cast_add,Int.cast_mul,Int.cast_ofNat,Int.cast_one]
  exact (div_le_iff₀ positive).mpr castBound

theorem ordered_right_digitalRoutes_disjoint {first second : GridSegment} {bound factor : Int}
    (boundNonnegative : 0 ≤ bound) (factorPositive : 0 < factor)
    (firstPositive : 0 < first.direction.1) (secondPositive : 0 < second.direction.1)
    (sameColumn : first.start.1 = second.start.1) (ports : first.start.2+2 ≤ second.start.2)
    (ordered : 0 ≤ cross first.direction second.direction) (slopeBound : |second.realSlope| ≤ bound)
    (spacing : 2*(bound+1) < factor) {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (first.scale factor).digitalRoute point) :
    ¬GridPolyline.RealContains (second.scale factor).digitalRoute point := by
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
  have realSpacing : 2*(2 : ℝ)*((bound : ℝ)+1) < 2*(factor : ℝ) := by
    have castSpacing : 2*((bound : ℝ)+1) < factor := by exact_mod_cast spacing
    linarith
  exact ordered_right_tubes_disjoint (by exact_mod_cast boundNonnegative) firstHorizontal secondHorizontal
    scaledColumn scaledPorts scaledOrder scaledSlope realSpacing
    ((first.scale factor).digitalRoute_tube firstContains) ((second.scale factor).digitalRoute_tube secondContains)

end LeanTrominoes.GridSegment
