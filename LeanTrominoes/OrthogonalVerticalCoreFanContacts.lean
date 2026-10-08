/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentVerticalCore
import LeanTrominoes.OrthogonalVertexHorizontalBoundaryLast
import LeanTrominoes.GridSegmentRealIntersection

/-! # A shortened vertical core touches an endpoint fan only at its outer anchor -/
namespace LeanTrominoes.OrthogonalDrawingRefinement

theorem verticalCore_fan_boundary {segment : GridSegment} (vertical : segment.IsVertical)
    {factor : Int} {radius : Nat} (spacing : 20*(radius : Int) < factor)
    {point : ℝ × ℝ} (coreContains : (segment.verticalCore factor radius).RealContains point)
    (target : Bool) (profile : AnchorProfile) (index : Fin 4)
    (fanContains : GridPolyline.RealContains (enlargedRectangleTemplate factor radius
      (if target then segment.finish else segment.start) profile index) point) :
    point.2-(factor : ℝ)*(if target then segment.finish else segment.start).2 = -10*(radius : ℝ) ∨
      point.2-(factor : ℝ)*(if target then segment.finish else segment.start).2 = 10*(radius : ℝ) := by
  have bounds := GridSegment.realBoxContains_of_realContains coreContains
  have fanBounds := abs_le.mp (enlargedRectangleTemplate_real_bounds factor radius _ profile index fanContains).2
  have order := GridSegment.verticalCore_order vertical spacing
  by_cases forward : segment.start.2 < segment.finish.2
  · simp only [if_pos forward] at order
    simp only [GridSegment.RealBoxContains,min_eq_left order.le,max_eq_right order.le] at bounds
    simp only [GridSegment.verticalCore,if_pos forward,Cell.add,Cell.scale] at bounds
    push_cast at bounds
    cases target
    · simp only [Bool.false_eq_true,if_false] at fanBounds ⊢
      exact Or.inr (by linarith [bounds.2.2.1,fanBounds.2])
    · simp only [if_true] at fanBounds ⊢
      exact Or.inl (by linarith [bounds.2.2.2,fanBounds.1])
  · simp only [if_neg forward] at order
    simp only [GridSegment.RealBoxContains,min_eq_right order.le,max_eq_left order.le] at bounds
    simp only [GridSegment.verticalCore,if_neg forward,Cell.add,Cell.scale] at bounds
    push_cast at bounds
    cases target
    · simp only [Bool.false_eq_true,if_false] at fanBounds ⊢
      exact Or.inl (by linarith [bounds.2.2.2,fanBounds.1])
    · simp only [if_true] at fanBounds ⊢
      exact Or.inr (by linarith [bounds.2.2.1,fanBounds.2])

theorem verticalCore_fan_contact_last {segment : GridSegment} (vertical : segment.IsVertical)
    {factor : Int} {radius : Nat} (positive : 0 < radius) (spacing : 20*(radius : Int) < factor)
    {point : ℝ × ℝ} (coreContains : (segment.verticalCore factor radius).RealContains point)
    (target : Bool) (profile : AnchorProfile) (index : Fin 4)
    (degree : profile.degree ≤ 4) (valid : index.val < profile.degree)
    (fanContains : GridPolyline.RealContains (enlargedRectangleTemplate factor radius
      (if target then segment.finish else segment.start) profile index) point) :
    point = realCell ((enlargedRectangleTemplate factor radius
      (if target then segment.finish else segment.start) profile index).getLast?.getD (0,0)) :=
  enlargedRectangleTemplate_horizontal_boundary_contact_last factor positive _ profile index degree valid fanContains
    (verticalCore_fan_boundary vertical spacing coreContains target profile index fanContains)

end LeanTrominoes.OrthogonalDrawingRefinement
