/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.OrthogonalVertexEnlargedTemplates
import LeanTrominoes.Common.Geometry.GridSegmentRealAxisBox

/-! # A vertex fan touches a horizontal side only at its terminal anchor -/
namespace LeanTrominoes.OrthogonalDrawingRefinement
open PeriodicOrthocrossing

theorem rectangleTemplate_horizontal_boundary_contact (profile : AnchorProfile) (index : Fin 4)
    (degree : profile.degree ≤ 4) (valid : index.val < profile.degree) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (rectangleTemplate profile index) point)
    (boundary : point.2 = -10 ∨ point.2 = 10) :
    point = realCell ((rectangleTemplate profile index).getLast?.getD (0,0)) := by
  have bounds := GridPolyline.realContains_bounds (rectangleTemplate_points_in_rectangle profile index) contains
  norm_num only [Int.cast_neg,Int.cast_ofNat] at bounds
  rcases boundary with south | north
  · apply rectangleTemplate_boundary_contact profile index .south degree valid contains
    have segmentContains : (⟨(-5,-10),(5,-10)⟩ : GridSegment).RealContains point := by
      apply GridSegment.realContains_of_axis_box (by simp [GridSegment.IsAxisAligned,GridSegment.IsHorizontal])
      norm_num [GridSegment.RealBoxContains,south]
      exact ⟨bounds.1,bounds.2.1⟩
    simpa [rectangleBoundaryRoute,GridPolyline.RealContains,gridPolylineSegments] using segmentContains
  · apply rectangleTemplate_boundary_contact profile index .north degree valid contains
    have segmentContains : (⟨(-5,10),(5,10)⟩ : GridSegment).RealContains point := by
      apply GridSegment.realContains_of_axis_box (by simp [GridSegment.IsAxisAligned,GridSegment.IsHorizontal])
      norm_num [GridSegment.RealBoxContains,north]
      exact ⟨bounds.1,bounds.2.1⟩
    simpa [rectangleBoundaryRoute,GridPolyline.RealContains,gridPolylineSegments] using segmentContains

theorem enlargedRectangleTemplate_horizontal_boundary_contact_endpoint (factor : Int) {radius : Nat} (positive : 0 < radius)
    (position : Cell) (profile : AnchorProfile) (index : Fin 4) (degree : profile.degree ≤ 4) (valid : index.val < profile.degree)
    {point : ℝ × ℝ} (contains : GridPolyline.RealContains (enlargedRectangleTemplate factor radius position profile index) point)
    (boundary : point.2-(factor : ℝ)*position.2 = -10*(radius : ℝ) ∨
      point.2-(factor : ℝ)*position.2 = 10*(radius : ℝ)) :
    GridPolyline.RealIsEndpoint (enlargedRectangleTemplate factor radius position profile index) point := by
  have nonzero : (radius : Int) ≠ 0 := by exact_mod_cast positive.ne'
  have realNonzero : (radius : ℝ) ≠ 0 := by exact_mod_cast positive.ne'
  have original := (GridPolyline.realContains_scale_inverse _ nonzero _).mp
    ((GridPolyline.realContains_translate_inverse _ _ _).mp contains)
  have originalBoundary : (point.2-(Cell.scale factor position).2)/(radius : ℝ) = -10 ∨
      (point.2-(Cell.scale factor position).2)/(radius : ℝ) = 10 := by
    simp only [Cell.scale,Int.cast_mul]
    rcases boundary with south | north
    · exact Or.inl ((div_eq_iff realNonzero).mpr (by linarith))
    · exact Or.inr ((div_eq_iff realNonzero).mpr (by linarith))
  have contact := rectangleTemplate_horizontal_boundary_contact profile index degree valid original originalBoundary
  have nonempty : rectangleTemplate profile index ≠ [] := by
    intro empty
    have long := (rectangleTemplate_isRealOpenSimple profile index).1
    simp [empty] at long
  have present : (rectangleTemplate profile index).getLast? ≠ none := by simpa using nonempty
  cases last : (rectangleTemplate profile index).getLast? with
  | none => exact (present last).elim
  | some anchor =>
    simp only [last,Option.getD_some] at contact
    refine Or.inr ⟨Cell.add (Cell.scale factor position) (Cell.scale radius anchor),?_,?_⟩
    · simp only [enlargedRectangleTemplate,translatePolyline,scalePolyline,List.getLast?_map,last,Option.map_some]
    · have x := (div_eq_iff realNonzero).mp (congrArg Prod.fst contact)
      have y := (div_eq_iff realNonzero).mp (congrArg Prod.snd contact)
      apply Prod.ext
      all_goals
        simp only [realCell,Cell.add,Cell.scale,Int.cast_add,Int.cast_mul,Int.cast_natCast] at x y ⊢
        linarith

end LeanTrominoes.OrthogonalDrawingRefinement
