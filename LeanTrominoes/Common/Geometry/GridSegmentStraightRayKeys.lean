/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentRationalOutwardRays
import LeanTrominoes.Common.Geometry.GridPolylineRealAlgebra

/-! # Rational keys for outward straight-edge rays -/
namespace LeanTrominoes

inductive StraightRayKey where
  | right (slope : ℚ)
  | left (slope : ℚ)
  | up
  | down
  deriving DecidableEq, Repr

def StraightRayKey.halfStep (key : StraightRayKey) (anchor : Cell) : ℚ × ℚ :=
  match key with
  | .right slope => rationalHorizontalHalfStep anchor true slope
  | .left slope => rationalHorizontalHalfStep anchor false slope
  | .up => ((anchor.1 : ℚ),(anchor.2 : ℚ)+1/2)
  | .down => ((anchor.1 : ℚ),(anchor.2 : ℚ)-1/2)

theorem StraightRayKey.halfStep_not_integral (key : StraightRayKey) (anchor point : Cell) :
    realRationalPoint (key.halfStep anchor) ≠ realCell point := by
  cases key with
  | right slope => exact rationalHorizontalHalfStep_not_integral anchor true slope point
  | left slope => exact rationalHorizontalHalfStep_not_integral anchor false slope point
  | up =>
    intro equal
    have hy := congrArg Prod.snd equal
    simp [halfStep,realRationalPoint,realCell] at hy
    have doubled : (2 : Int)*point.2 = 2*anchor.2+1 := by
      exact_mod_cast (by linarith : (2 : ℝ)*point.2 = 2*anchor.2+1)
    omega
  | down =>
    intro equal
    have hy := congrArg Prod.snd equal
    simp [halfStep,realRationalPoint,realCell] at hy
    have doubled : (2 : Int)*point.2 = 2*anchor.2-1 := by
      exact_mod_cast (by linarith : (2 : ℝ)*point.2 = 2*anchor.2-1)
    omega

namespace GridSegment

def straightRayKey (segment : GridSegment) : StraightRayKey :=
  if segment.start.1 < segment.finish.1 then .right segment.rationalSlope
  else if segment.finish.1 < segment.start.1 then .left segment.rationalSlope
  else if segment.start.2 < segment.finish.2 then .up else .down

theorem straightRayKey_reverse_ne {segment : GridSegment} (nondegenerate : segment.start ≠ segment.finish) :
    segment.straightRayKey ≠ segment.reverse.straightRayKey := by
  by_cases right : segment.start.1 < segment.finish.1
  · have notLeft : ¬segment.finish.1 < segment.start.1 := by omega
    simp [straightRayKey,reverse,right,notLeft]
  by_cases left : segment.finish.1 < segment.start.1
  · simp [straightRayKey,reverse,right,left]
  have sameX : segment.start.1 = segment.finish.1 := by omega
  have differentY : segment.start.2 ≠ segment.finish.2 := by
    intro sameY
    exact nondegenerate (Prod.ext sameX sameY)
  by_cases up : segment.start.2 < segment.finish.2
  · have notDown : ¬segment.finish.2 < segment.start.2 := by omega
    simp [straightRayKey,reverse,right,left,up,notDown]
  · have down : segment.finish.2 < segment.start.2 := by omega
    simp [straightRayKey,reverse,right,left,up,down]

theorem realContains_straightRay_halfStep {segment : GridSegment} (nondegenerate : segment.start ≠ segment.finish) :
    segment.RealContains (realRationalPoint (segment.straightRayKey.halfStep segment.start)) := by
  by_cases right : segment.start.1 < segment.finish.1
  · simpa [straightRayKey,right,StraightRayKey.halfStep] using
      realContains_horizontal_halfStep (segment := segment) (by omega)
  by_cases left : segment.finish.1 < segment.start.1
  · have notRight : ¬segment.start.1 < segment.finish.1 := by omega
    simpa [straightRayKey,right,left,StraightRayKey.halfStep,notRight] using
      realContains_horizontal_halfStep (segment := segment) (by omega)
  have sameX : segment.start.1 = segment.finish.1 := by omega
  have differentY : segment.start.2 ≠ segment.finish.2 := by
    intro sameY
    exact nondegenerate (Prod.ext sameX sameY)
  by_cases up : segment.start.2 < segment.finish.2
  · have positive : (0 : ℝ) < segment.finish.2-segment.start.2 := by
      exact_mod_cast (by omega : (0 : Int) < segment.finish.2-segment.start.2)
    have unit : (1 : ℝ) ≤ segment.finish.2-segment.start.2 := by
      exact_mod_cast (by omega : (1 : Int) ≤ segment.finish.2-segment.start.2)
    refine ⟨1/(2*((segment.finish.2 : ℝ)-segment.start.2)),div_nonneg (by norm_num) (by positivity),?_,?_,?_⟩
    · apply (div_le_one (by positivity : (0 : ℝ) < 2*((segment.finish.2 : ℝ)-segment.start.2))).mpr
      linarith
    · simp [straightRayKey,right,left,up,StraightRayKey.halfStep,realRationalPoint,sameX]
    · simp only [straightRayKey,right,left,up,ite_false,ite_true,StraightRayKey.halfStep,realRationalPoint]
      push_cast
      field_simp [positive.ne'] <;> ring
  · have positive : (0 : ℝ) < segment.start.2-segment.finish.2 := by
      exact_mod_cast (by omega : (0 : Int) < segment.start.2-segment.finish.2)
    have unit : (1 : ℝ) ≤ segment.start.2-segment.finish.2 := by
      exact_mod_cast (by omega : (1 : Int) ≤ segment.start.2-segment.finish.2)
    refine ⟨1/(2*((segment.start.2 : ℝ)-segment.finish.2)),div_nonneg (by norm_num) (by positivity),?_,?_,?_⟩
    · apply (div_le_one (by positivity : (0 : ℝ) < 2*((segment.start.2 : ℝ)-segment.finish.2))).mpr
      linarith
    · simp [straightRayKey,right,left,up,StraightRayKey.halfStep,realRationalPoint,sameX]
    · simp only [straightRayKey,right,left,up,ite_false,StraightRayKey.halfStep,realRationalPoint]
      push_cast
      field_simp [positive.ne'] <;> ring

end GridSegment
end LeanTrominoes
