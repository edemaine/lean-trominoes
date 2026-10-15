/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.OrthogonalVertexEnlargedTemplates

/-! # Wide crossing bars avoid enlarged vertex connectors -/
namespace LeanTrominoes.OrthogonalDrawingRefinement
open PeriodicOrthocrossing

def enlargedCrossingBar (factor : Int) (radius : Nat) (line ordinate : Int) : List Cell :=
  [(factor*line-5*radius,ordinate),(factor*line+5*radius,ordinate)]

theorem enlargedCrossingBar_isRealOpenSimple (factor : Int) {radius : Nat} (positive : 0 < radius) (line ordinate : Int) :
    GridPolyline.IsRealOpenSimple (enlargedCrossingBar factor radius line ordinate) := by
  apply GridPolyline.isRealOpenSimple_of_box_certificate
  simp [enlargedCrossingBar,GridPolyline.SimpleBoxCertificate,gridPolylineSegments]
  omega

theorem enlargedCrossingBar_orthogonal (factor : Int) {radius : Nat} (positive : 0 < radius) (line ordinate : Int) :
    OrthogonalPolyline (enlargedCrossingBar factor radius line ordinate) := by
  simp [enlargedCrossingBar,OrthogonalPolyline,GridSegment.IsAxisAligned,GridSegment.IsHorizontal]
  left
  omega

theorem enlargedCrossingBar_real_bounds (factor : Int) (radius : Nat) (line ordinate : Int) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (enlargedCrossingBar factor radius line ordinate) point) :
    |point.1-(factor : ℝ)*line| ≤ 5*(radius : ℝ) ∧ point.2 = (ordinate : ℝ) := by
  have member : (⟨(factor*line-5*radius,ordinate),(factor*line+5*radius,ordinate)⟩ : GridSegment).RealContains point := by
    simpa [enlargedCrossingBar,GridPolyline.RealContains,gridPolylineSegments] using contains
  have bounds := GridSegment.realBoxContains_of_realContains member
  simp only [GridSegment.RealBoxContains] at bounds
  have nonnegative : (0 : Int) ≤ radius := by positivity
  have xOrder : factor*line-5*radius ≤ factor*line+5*radius := by omega
  simp only [min_eq_left xOrder,max_eq_right xOrder,min_self,max_self] at bounds
  push_cast at bounds
  exact ⟨abs_le.mpr ⟨by linarith [bounds.1],by linarith [bounds.2.1]⟩,le_antisymm bounds.2.2.2 bounds.2.2.1⟩

theorem enlargedCrossingBars_disjoint (factor : Int) (radius : Nat) (line first second : Int) (different : first ≠ second) {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (enlargedCrossingBar factor radius line first) point)
    (secondContains : GridPolyline.RealContains (enlargedCrossingBar factor radius line second) point) : False := by
  have equal := (enlargedCrossingBar_real_bounds factor radius line first firstContains).2.symm.trans
    (enlargedCrossingBar_real_bounds factor radius line second secondContains).2
  exact different (by exact_mod_cast equal)

theorem enlargedCrossingBar_avoids_rectangle {factor line ordinate : Int} {radius : Nat} (spacing : 10*(radius : Int) < factor)
    {position : Cell} (profile : AnchorProfile) (index : Fin 4)
    (clearance : position.1 = line → 10*(radius : Int) < |ordinate-factor*position.2|) {point : ℝ × ℝ}
    (barContains : GridPolyline.RealContains (enlargedCrossingBar factor radius line ordinate) point)
    (templateContains : GridPolyline.RealContains (enlargedRectangleTemplate factor radius position profile index) point) : False := by
  have barBounds := enlargedCrossingBar_real_bounds factor radius line ordinate barContains
  have templateBounds := enlargedRectangleTemplate_real_bounds factor radius position profile index templateContains
  have radiusNonnegative : (0 : Int) ≤ radius := by positivity
  have sameX : position.1 = line := by
    apply GridSegment.closed_interval_periodic_shifts_unique (period := factor) (lower := -5*(radius : Int)) (upper := 5*radius)
      (point := point.1) (by omega) (by omega)
    · push_cast
      exact ⟨by linarith [(abs_le.mp templateBounds.1).1],by linarith [(abs_le.mp templateBounds.1).2]⟩
    · push_cast
      exact ⟨by linarith [(abs_le.mp barBounds.1).1],by linarith [(abs_le.mp barBounds.1).2]⟩
  have gap := clearance sameX
  have gapReal : 10*(radius : ℝ) < |(ordinate : ℝ)-(factor : ℝ)*position.2| := by exact_mod_cast gap
  rw [barBounds.2] at templateBounds
  linarith [templateBounds.2]

end LeanTrominoes.OrthogonalDrawingRefinement
