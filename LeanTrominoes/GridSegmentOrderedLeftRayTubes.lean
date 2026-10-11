/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentKickedCoreDigitalRoutes

/-! # Tube separation on the left side of a vertex fan -/
namespace LeanTrominoes.GridSegment

def mirrorX (segment : GridSegment) : GridSegment :=
  ⟨(-segment.start.1,segment.start.2),(-segment.finish.1,segment.finish.2)⟩

theorem realContains_mirrorX (segment : GridSegment) (point : ℝ × ℝ) :
    segment.mirrorX.RealContains (-point.1,point.2) ↔ segment.RealContains point := by
  unfold RealContains mirrorX
  simp only [Int.cast_neg]
  constructor <;> rintro ⟨t,lower,upper,x,y⟩ <;>
    exact ⟨t,lower,upper,by linarith,y⟩

theorem RealTubeContains.mirrorX {segment : GridSegment} {radius : ℝ} {point : ℝ × ℝ}
    (contains : segment.RealTubeContains radius point) :
    segment.mirrorX.RealTubeContains radius (-point.1,point.2) := by
  obtain ⟨original,originalContains,x,y⟩ := contains
  refine ⟨(-original.1,original.2),(realContains_mirrorX segment original).mpr originalContains,?_,y⟩
  change |-point.1- -original.1| ≤ radius
  rw [show -point.1- -original.1 = -(point.1-original.1) by ring,abs_neg]
  exact x

theorem direction_mirrorX (segment : GridSegment) :
    segment.mirrorX.direction = (-segment.direction.1,segment.direction.2) := by
  simp only [direction,mirrorX]
  apply Prod.ext <;> ring

theorem realSlope_mirrorX (segment : GridSegment) : segment.mirrorX.realSlope = -segment.realSlope := by
  simp only [realSlope,direction_mirrorX,Int.cast_neg,div_neg]

theorem cross_mirrored_directions (first second : GridSegment) :
    cross first.mirrorX.direction second.mirrorX.direction = -cross first.direction second.direction := by
  simp only [direction_mirrorX,cross]
  ring

theorem ordered_left_tubes_disjoint {first second : GridSegment} {bound gap radius : ℝ}
    (boundNonnegative : 0 ≤ bound)
    (firstNegative : first.direction.1 < 0) (secondNegative : second.direction.1 < 0)
    (sameColumn : first.start.1 = second.start.1)
    (ports : (first.start.2 : ℝ)+gap ≤ second.start.2)
    (ordered : cross first.direction second.direction ≤ 0)
    (slopeBound : |second.realSlope| ≤ bound) (spacing : 2*radius*(bound+1) < gap)
    {point : ℝ × ℝ} (firstContains : first.RealTubeContains radius point) :
    ¬second.RealTubeContains radius point := by
  intro secondContains
  apply ordered_right_tubes_disjoint (first := first.mirrorX) (second := second.mirrorX)
    boundNonnegative
    (by simp only [direction_mirrorX]; omega) (by simp only [direction_mirrorX]; omega)
    (by simp only [mirrorX,sameColumn]) ports
    (by rw [cross_mirrored_directions]; omega)
    (by simpa only [realSlope_mirrorX,abs_neg] using slopeBound) spacing
    firstContains.mirrorX secondContains.mirrorX

theorem ordered_left_kickedDigitalRoutes_disjoint {first second : GridSegment} {bound factor : Int}
    (boundNonnegative : 0 ≤ bound) (factorPositive : 0 < factor)
    (firstNegative : first.direction.1 < 0) (secondNegative : second.direction.1 < 0)
    (sameColumn : first.start.1 = second.start.1) (ports : first.start.2+2 ≤ second.start.2)
    (ordered : cross first.direction second.direction ≤ 0) (slopeBound : |second.realSlope| ≤ bound)
    (spacing : 3*(bound+1) < factor) {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains ((first.scale factor).kickedDigitalRoute (-1)) point) :
    ¬GridPolyline.RealContains ((second.scale factor).kickedDigitalRoute (-1)) point := by
  intro secondContains
  have firstHorizontal : (first.scale factor).direction.1 < 0 := by
    simp only [direction_scale,Cell.scale]
    exact mul_neg_of_pos_of_neg factorPositive firstNegative
  have secondHorizontal : (second.scale factor).direction.1 < 0 := by
    simp only [direction_scale,Cell.scale]
    exact mul_neg_of_pos_of_neg factorPositive secondNegative
  have scaledColumn : (first.scale factor).start.1 = (second.scale factor).start.1 := by
    simp only [scale,Cell.scale,sameColumn]
  have scaledPorts : ((first.scale factor).start.2 : ℝ)+2*(factor : ℝ) ≤ (second.scale factor).start.2 := by
    have scaled := mul_le_mul_of_nonneg_left ports factorPositive.le
    have scaled' : factor*first.start.2+2*factor ≤ factor*second.start.2 := by nlinarith
    simp only [scale,Cell.scale,Int.cast_mul]
    exact_mod_cast scaled'
  have scaledOrder : cross (first.scale factor).direction (second.scale factor).direction ≤ 0 := by
    rw [cross_scaled_directions]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) ordered
  have scaledSlope : |(second.scale factor).realSlope| ≤ (bound : ℝ) := by
    rw [realSlope_scale second (ne_of_gt factorPositive)]
    exact slopeBound
  have realSpacing : 2*(3 : ℝ)*((bound : ℝ)+1) < 2*(factor : ℝ) := by
    have castSpacing : 3*((bound : ℝ)+1) < factor := by exact_mod_cast spacing
    linarith
  exact ordered_left_tubes_disjoint (by exact_mod_cast boundNonnegative) firstHorizontal secondHorizontal
    scaledColumn scaledPorts scaledOrder scaledSlope realSpacing
    ((first.scale factor).kickedDigitalRoute_tube (by norm_num) (by norm_num) firstContains)
    ((second.scale factor).kickedDigitalRoute_tube (by norm_num) (by norm_num) secondContains)

end LeanTrominoes.GridSegment
