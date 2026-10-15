/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentRationalVerticalCrossing
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRealGeometry

/-! # Half-unit horizontal rays distinguish incident straight-edge slopes -/
namespace LeanTrominoes

def rationalHorizontalHalfStep (anchor : Cell) (right : Bool) (slope : ℚ) : ℚ × ℚ :=
  ((anchor.1 : ℚ)+(if right then 1/2 else -1/2),
    (anchor.2 : ℚ)+(if right then 1/2 else -1/2)*slope)

def realRationalPoint (point : ℚ × ℚ) : ℝ × ℝ := (point.1,point.2)

theorem rationalHorizontalHalfStep_not_integral (anchor : Cell) (right : Bool) (slope : ℚ) (point : Cell) :
    realRationalPoint (rationalHorizontalHalfStep anchor right slope) ≠ realCell point := by
  intro equal
  have hx := congrArg Prod.fst equal
  cases right <;> simp [realRationalPoint,rationalHorizontalHalfStep,realCell] at hx
  all_goals
    have doubled : (2 : Int)*point.1 = 2*anchor.1+1 ∨ (2 : Int)*point.1 = 2*anchor.1-1 := by
      first
      | apply Or.inl; exact_mod_cast (by linarith : (2 : ℝ)*point.1 = 2*anchor.1+1)
      | apply Or.inr; exact_mod_cast (by linarith : (2 : ℝ)*point.1 = 2*anchor.1-1)
    omega

namespace GridSegment

def rationalSlope (segment : GridSegment) : ℚ :=
  ((segment.finish.2 : ℚ)-segment.start.2)/((segment.finish.1 : ℚ)-segment.start.1)

theorem realContains_horizontal_halfStep {segment : GridSegment} (nonvertical : segment.start.1 ≠ segment.finish.1) :
    segment.RealContains (realRationalPoint (rationalHorizontalHalfStep segment.start
      (decide (segment.start.1 < segment.finish.1)) segment.rationalSlope)) := by
  by_cases right : segment.start.1 < segment.finish.1
  · have positive : (0 : ℝ) < segment.finish.1-segment.start.1 := by
      exact_mod_cast (by omega : (0 : Int) < segment.finish.1-segment.start.1)
    have unit : (1 : ℝ) ≤ segment.finish.1-segment.start.1 := by
      exact_mod_cast (by omega : (1 : Int) ≤ segment.finish.1-segment.start.1)
    refine ⟨1/(2*((segment.finish.1 : ℝ)-segment.start.1)),div_nonneg (by norm_num) (by positivity),?_,?_,?_⟩
    · apply (div_le_one (by positivity : (0 : ℝ) < 2*((segment.finish.1 : ℝ)-segment.start.1))).mpr
      linarith
    · simp only [realRationalPoint,rationalHorizontalHalfStep,right,decide_true,ite_true,Prod.fst]
      push_cast
      field_simp [positive.ne'] <;> ring
    · simp only [realRationalPoint,rationalHorizontalHalfStep,rationalSlope,right,decide_true,ite_true,Prod.snd]
      push_cast
      field_simp [positive.ne'] <;> ring
  · have positive : (0 : ℝ) < segment.start.1-segment.finish.1 := by
      exact_mod_cast (by omega : (0 : Int) < segment.start.1-segment.finish.1)
    have unit : (1 : ℝ) ≤ segment.start.1-segment.finish.1 := by
      exact_mod_cast (by omega : (1 : Int) ≤ segment.start.1-segment.finish.1)
    refine ⟨1/(2*((segment.start.1 : ℝ)-segment.finish.1)),div_nonneg (by norm_num) (by positivity),?_,?_,?_⟩
    · apply (div_le_one (by positivity : (0 : ℝ) < 2*((segment.start.1 : ℝ)-segment.finish.1))).mpr
      linarith
    · simp only [realRationalPoint,rationalHorizontalHalfStep,right,decide_false,ite_false,Prod.fst]
      push_cast
      field_simp [positive.ne'] <;> ring
    · have oppositeNonzero : (segment.finish.1 : ℝ)-segment.start.1 ≠ 0 := by linarith
      simp only [realRationalPoint,rationalHorizontalHalfStep,rationalSlope,right,decide_false,ite_false,Prod.snd]
      push_cast
      field_simp [positive.ne',oppositeNonzero] <;> ring

end GridSegment
end LeanTrominoes
