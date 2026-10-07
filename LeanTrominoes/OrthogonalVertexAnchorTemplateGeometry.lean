/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.OrthogonalVertexAnchorTemplateContacts
import LeanTrominoes.GridSegmentCollinearRectangleSeparation
import LeanTrominoes.GridPolylineRealPeriodicSeparation
import LeanTrominoes.GridPolylineRealAffineSimplicity

/-! # Rectangle connectors are isolated from nonincident input segments -/
namespace LeanTrominoes.OrthogonalDrawingRefinement
open PeriodicOrthocrossing

def rectangleTemplateAt (factor : Int) (position : Cell) (profile : AnchorProfile) (index : Fin 4) : List Cell :=
  translatePolyline (Cell.scale factor position) (rectangleTemplate profile index)

theorem rectangleTemplateAt_isRealOpenSimple (factor : Int) (position : Cell) (profile : AnchorProfile) (index : Fin 4) :
    GridPolyline.IsRealOpenSimple (rectangleTemplateAt factor position profile index) :=
  (rectangleTemplate_isRealOpenSimple profile index).translate _

theorem rectangleTemplateAt_real_bounds (factor : Int) (position : Cell) (profile : AnchorProfile) (index : Fin 4)
    {point : ℝ × ℝ} (contains : GridPolyline.RealContains (rectangleTemplateAt factor position profile index) point) :
    |point.1-(factor : ℝ)*position.1| ≤ 5 ∧ |point.2-(factor : ℝ)*position.2| ≤ 10 := by
  have original := (GridPolyline.realContains_translate_inverse _ _ _).mp contains
  have bounds := GridPolyline.realContains_bounds (rectangleTemplate_points_in_rectangle profile index) original
  simp only [Cell.scale,Int.cast_mul] at bounds
  norm_num only [Int.cast_neg,Int.cast_ofNat] at bounds
  exact ⟨abs_le.mpr ⟨by linarith [bounds.1],by linarith [bounds.2.1]⟩,
    abs_le.mpr ⟨by linarith [bounds.2.2.1],by linarith [bounds.2.2.2]⟩⟩

theorem rectangleTemplateAt_contacts_same_position {factor : Int} (spacing : 20 < factor)
    {firstPosition secondPosition : Cell} (firstProfile secondProfile : AnchorProfile) (first second : Fin 4)
    {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (rectangleTemplateAt factor firstPosition firstProfile first) point)
    (secondContains : GridPolyline.RealContains (rectangleTemplateAt factor secondPosition secondProfile second) point) :
    firstPosition = secondPosition := by
  have fb := rectangleTemplateAt_real_bounds factor firstPosition firstProfile first firstContains
  have sb := rectangleTemplateAt_real_bounds factor secondPosition secondProfile second secondContains
  apply Prod.ext
  · apply GridSegment.closed_interval_periodic_shifts_unique (period := factor) (lower := -5) (upper := 5)
      (point := point.1) (by omega) (by omega)
    · norm_num only [Int.cast_neg,Int.cast_ofNat]
      exact ⟨by linarith [(abs_le.mp fb.1).1],by linarith [(abs_le.mp fb.1).2]⟩
    · norm_num only [Int.cast_neg,Int.cast_ofNat]
      exact ⟨by linarith [(abs_le.mp sb.1).1],by linarith [(abs_le.mp sb.1).2]⟩
  · apply GridSegment.closed_interval_periodic_shifts_unique (period := factor) (lower := -10) (upper := 10)
      (point := point.2) (by omega) (by omega)
    · norm_num only [Int.cast_neg,Int.cast_ofNat]
      exact ⟨by linarith [(abs_le.mp fb.2).1],by linarith [(abs_le.mp fb.2).2]⟩
    · norm_num only [Int.cast_neg,Int.cast_ofNat]
      exact ⟨by linarith [(abs_le.mp sb.2).1],by linarith [(abs_le.mp sb.2).2]⟩

theorem rectangleTemplateAt_avoids_nonincident_segment {segment : GridSegment} {position : Cell}
    {grid factor : Int} (gridNonnegative : 0 ≤ grid) (spacing : 30*grid+10 < factor)
    (horizontalBound : |segment.finish.1-segment.start.1| ≤ 2*grid)
    (verticalBound : |segment.finish.2-segment.start.2| ≤ 2*grid)
    (nonincident : ¬ segment.RealContains (realCell position)) (profile : AnchorProfile) (index : Fin 4) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (rectangleTemplateAt factor position profile index) point) :
    ¬ (segment.scale factor).RealContains point := by
  have bounds := rectangleTemplateAt_real_bounds factor position profile index contains
  exact GridSegment.vertex_rectangle_avoids_nonincident_segment gridNonnegative spacing horizontalBound verticalBound
    nonincident bounds.1 bounds.2

end LeanTrominoes.OrthogonalDrawingRefinement
