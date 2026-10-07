/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingColumnRefinement
import LeanTrominoes.OrthogonalVertexAnchorTemplateGeometry
import LeanTrominoes.GridSegmentRealAxisBox

/-! # Horizontal crossing bars clear every rectangle connector -/
namespace LeanTrominoes.OrthogonalDrawingRefinement
open PeriodicOrthocrossing

def crossingBar (factor line ordinate : Int) : List Cell :=
  [(factor*line-5,ordinate),(factor*line+5,ordinate)]

theorem crossingBar_isRealOpenSimple (factor line ordinate : Int) : GridPolyline.IsRealOpenSimple (crossingBar factor line ordinate) := by
  apply GridPolyline.isRealOpenSimple_of_box_certificate
  simp [crossingBar,GridPolyline.SimpleBoxCertificate,gridPolylineSegments]
  omega

theorem crossingBar_orthogonal (factor line ordinate : Int) : OrthogonalPolyline (crossingBar factor line ordinate) := by
  simp [crossingBar,OrthogonalPolyline,GridSegment.IsAxisAligned,GridSegment.IsHorizontal]
  left
  omega

theorem crossingBar_real_bounds (factor line ordinate : Int) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (crossingBar factor line ordinate) point) :
    |point.1-(factor : ℝ)*line| ≤ 5 ∧ point.2 = (ordinate : ℝ) := by
  have member : (⟨(factor*line-5,ordinate),(factor*line+5,ordinate)⟩ : GridSegment).RealContains point := by
    simpa [crossingBar,GridPolyline.RealContains,gridPolylineSegments] using contains
  have bounds := GridSegment.realBoxContains_of_realContains member
  simp only [GridSegment.RealBoxContains] at bounds
  have xOrder : factor*line-5 ≤ factor*line+5 := by omega
  simp only [min_eq_left xOrder,max_eq_right xOrder,min_self,max_self] at bounds
  push_cast at bounds
  exact ⟨abs_le.mpr ⟨by linarith [bounds.1],by linarith [bounds.2.1]⟩,le_antisymm bounds.2.2.2 bounds.2.2.1⟩

theorem crossingBars_disjoint (factor line first second : Int) (different : first ≠ second) {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (crossingBar factor line first) point)
    (secondContains : GridPolyline.RealContains (crossingBar factor line second) point) : False := by
  have equal := (crossingBar_real_bounds factor line first firstContains).2.symm.trans
    (crossingBar_real_bounds factor line second secondContains).2
  exact different (by exact_mod_cast equal)

theorem crossingBar_avoids_rectangle {factor line ordinate : Int} (spacing : 10 < factor)
    {position : Cell} (profile : AnchorProfile) (index : Fin 4)
    (clearance : position.1 = line → 10 < |ordinate-factor*position.2|) {point : ℝ × ℝ}
    (barContains : GridPolyline.RealContains (crossingBar factor line ordinate) point)
    (templateContains : GridPolyline.RealContains (rectangleTemplateAt factor position profile index) point) : False := by
  have barBounds := crossingBar_real_bounds factor line ordinate barContains
  have templateBounds := rectangleTemplateAt_real_bounds factor position profile index templateContains
  have sameX : position.1 = line := by
    apply GridSegment.closed_interval_periodic_shifts_unique (period := factor) (lower := -5) (upper := 5)
      (point := point.1) (by omega) (by omega)
    · norm_num only [Int.cast_neg,Int.cast_ofNat]
      exact ⟨by linarith [(abs_le.mp templateBounds.1).1],by linarith [(abs_le.mp templateBounds.1).2]⟩
    · norm_num only [Int.cast_neg,Int.cast_ofNat]
      exact ⟨by linarith [(abs_le.mp barBounds.1).1],by linarith [(abs_le.mp barBounds.1).2]⟩
  have gap := clearance sameX
  have gapReal : (10 : ℝ) < |(ordinate : ℝ)-(factor : ℝ)*position.2| := by exact_mod_cast gap
  rw [barBounds.2] at templateBounds
  linarith [templateBounds.2]

end OrthogonalDrawingRefinement

namespace PeriodicGridDrawing
open OrthogonalDrawingRefinement

theorem redistributedCrossingHeight_avoids_vertex {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    (degree : graph.DegreeAtMost 4) {line : Int} {height : ℚ}
    (member : height ∈ verticalCrossingHeights graph drawing line) {point : Cell}
    (pointMember : point ∈ drawing.vertexPositions) (sameX : point.1 = line) :
    10 < |redistributedCrossingHeight graph drawing line height-(refinementFactor drawing.gridSize : Int)*point.2| := by
  have present := column_bracket_present member
  have levelMember := columnLevels_vertex pointMember sameX
  have countBound : ((verticalCrossingHeights graph drawing line).card : Int) ≤ crossingBound drawing.gridSize := by
    exact_mod_cast verticalCrossingHeights_card_bound compatible degree line
  by_cases below : height < (point.2 : ℚ)
  · have gap := redistributedHeight_below_vertex member present.1 present.2 countBound levelMember below
    rw [vertexCoordinate_eq_factor] at gap
    change 10 < |redistributedHeight _ _ _ _-_|
    rw [abs_of_neg (by omega)]
    omega
  · have gap := redistributedHeight_above_vertex member present.1 present.2 countBound levelMember (le_of_not_gt below)
    rw [vertexCoordinate_eq_factor] at gap
    change 10 < |redistributedHeight _ _ _ _-_|
    rw [abs_of_pos (by omega)]
    omega

theorem redistributedCrossingBar_avoids_rectangle {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    (degree : graph.DegreeAtMost 4) {line : Int} {height : ℚ}
    (member : height ∈ verticalCrossingHeights graph drawing line) {position : Cell}
    (positionMember : position ∈ drawing.vertexPositions) (profile : AnchorProfile) (index : Fin 4) {point : ℝ × ℝ}
    (barContains : GridPolyline.RealContains
      (crossingBar (refinementFactor drawing.gridSize) line (redistributedCrossingHeight graph drawing line height)) point)
    (templateContains : GridPolyline.RealContains
      (rectangleTemplateAt (refinementFactor drawing.gridSize) position profile index) point) : False := by
  have gridPositive : 0 < drawing.gridSize := by unfold PeriodicGridDrawing.gridSize; omega
  have spacing := refinementFactor_isolates_rectangles gridPositive
  exact crossingBar_avoids_rectangle (by omega) profile index
    (redistributedCrossingHeight_avoids_vertex compatible degree member positionMember) barContains templateContains

end PeriodicGridDrawing
end LeanTrominoes
