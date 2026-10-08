/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentRealConvexity
import LeanTrominoes.PeriodicGridDrawingScaling
import LeanTrominoes.GridSegmentRealIntersection

/-! # A vertical segment shortened by the radius of its endpoint fans -/
namespace LeanTrominoes.GridSegment

def verticalCore (segment : GridSegment) (factor : Int) (radius : Nat) : GridSegment :=
  let step : Int := if segment.start.2 < segment.finish.2 then 10 else -10
  ⟨Cell.add (Cell.scale factor segment.start) (Cell.scale radius (0,step)),
    Cell.add (Cell.scale factor segment.finish) (Cell.scale radius (0,-step))⟩

theorem verticalCore_isVertical {segment : GridSegment} (vertical : segment.IsVertical)
    {factor : Int} {radius : Nat} (spacing : 20*(radius : Int) < factor) :
    (segment.verticalCore factor radius).IsVertical := by
  have nonnegative : (0 : Int) ≤ radius := by positivity
  have factorPositive : 0 < factor := by omega
  have differentY := vertical.2
  by_cases forward : segment.start.2 < segment.finish.2
  · have gap : segment.start.2+1 ≤ segment.finish.2 := by omega
    refine ⟨?_,?_⟩
    · simp [verticalCore,Cell.add,Cell.scale,forward,vertical.1]
    · simp only [verticalCore,if_pos forward,Cell.add,Cell.scale]
      intro equal
      nlinarith only [equal,gap,spacing,nonnegative,factorPositive]
  · have gap : segment.finish.2+1 ≤ segment.start.2 := by omega
    refine ⟨?_,?_⟩
    · simp [verticalCore,Cell.add,Cell.scale,forward,vertical.1]
    · simp only [verticalCore,if_neg forward,Cell.add,Cell.scale]
      intro equal
      nlinarith only [equal,gap,spacing,nonnegative,factorPositive]

theorem verticalCore_order {segment : GridSegment} (vertical : segment.IsVertical)
    {factor : Int} {radius : Nat} (spacing : 20*(radius : Int) < factor) :
    if segment.start.2 < segment.finish.2 then
      (segment.verticalCore factor radius).start.2 < (segment.verticalCore factor radius).finish.2
    else (segment.verticalCore factor radius).finish.2 < (segment.verticalCore factor radius).start.2 := by
  have nonnegative : (0 : Int) ≤ radius := by positivity
  have factorPositive : 0 < factor := by omega
  have differentY := vertical.2
  split_ifs with forward
  · have gap : segment.start.2+1 ≤ segment.finish.2 := by omega
    simp only [verticalCore,if_pos forward,Cell.add,Cell.scale]
    nlinarith only [gap,spacing,nonnegative,factorPositive]
  · have gap : segment.finish.2+1 ≤ segment.start.2 := by omega
    simp only [verticalCore,if_neg forward,Cell.add,Cell.scale]
    nlinarith only [gap,spacing,nonnegative,factorPositive]

theorem verticalCore_endpoints_contained {segment : GridSegment} (vertical : segment.IsVertical)
    {factor : Int} {radius : Nat} (spacing : 20*(radius : Int) < factor) :
    (segment.scale factor).Contains (segment.verticalCore factor radius).start ∧
      (segment.scale factor).Contains (segment.verticalCore factor radius).finish := by
  have nonnegative : (0 : Int) ≤ radius := by positivity
  have factorPositive : 0 < factor := by omega
  have differentY := vertical.2
  have scaledVertical : (segment.scale factor).IsVertical := by
    refine ⟨by simp [scale,Cell.scale,vertical.1],?_⟩
    simp only [scale,Cell.scale]
    exact fun equal => vertical.2 (mul_left_cancel₀ factorPositive.ne' equal)
  by_cases forward : segment.start.2 < segment.finish.2
  · have gap : segment.start.2+1 ≤ segment.finish.2 := by omega
    constructor
    all_goals refine Or.inr ⟨scaledVertical,?_,Or.inl ⟨?_,?_⟩⟩
    all_goals simp only [verticalCore,if_pos forward,Cell.add,Cell.scale,scale,vertical.1,mul_zero,add_zero]
    all_goals first | rfl | nlinarith only [gap,spacing,nonnegative,factorPositive]
  · have gap : segment.finish.2+1 ≤ segment.start.2 := by omega
    constructor
    all_goals refine Or.inr ⟨scaledVertical,?_,Or.inr ⟨?_,?_⟩⟩
    all_goals simp only [verticalCore,if_neg forward,Cell.add,Cell.scale,scale,vertical.1,mul_zero,add_zero]
    all_goals first | rfl | nlinarith only [gap,spacing,nonnegative,factorPositive]

theorem verticalCore_realContains_parent {segment : GridSegment} (vertical : segment.IsVertical)
    {factor : Int} {radius : Nat} (spacing : 20*(radius : Int) < factor)
    {point : ℝ × ℝ} (contains : (segment.verticalCore factor radius).RealContains point) :
    (segment.scale factor).RealContains point := by
  have ends := verticalCore_endpoints_contained vertical spacing
  exact realContains_of_endpoints_contained (realContains_of_contains ends.1)
    (realContains_of_contains ends.2) contains

theorem verticalCore_avoids_scaled_endpoint {segment : GridSegment} (vertical : segment.IsVertical)
    {factor : Int} {radius : Nat} (positive : 0 < radius) (spacing : 20*(radius : Int) < factor)
    (target : Bool) :
    ¬ (segment.verticalCore factor radius).RealContains
      (realCell (Cell.scale factor (if target then segment.finish else segment.start))) := by
  intro contains
  have box := realBoxContains_of_realContains contains
  have order := verticalCore_order vertical spacing
  have radiusPositive : (0 : ℝ) < radius := by exact_mod_cast positive
  by_cases forward : segment.start.2 < segment.finish.2
  · simp only [if_pos forward] at order
    simp only [RealBoxContains,min_eq_left order.le,max_eq_right order.le] at box
    cases target
    all_goals simp only [Bool.false_eq_true,if_false,if_true,realCell,verticalCore,if_pos forward,Cell.add,Cell.scale] at box
    all_goals push_cast at box
    all_goals linarith [box.2.2.1,box.2.2.2]
  · simp only [if_neg forward] at order
    simp only [RealBoxContains,min_eq_right order.le,max_eq_left order.le] at box
    cases target
    all_goals simp only [Bool.false_eq_true,if_false,if_true,realCell,verticalCore,if_neg forward,Cell.add,Cell.scale] at box
    all_goals push_cast at box
    all_goals linarith [box.2.2.1,box.2.2.2]

end LeanTrominoes.GridSegment
