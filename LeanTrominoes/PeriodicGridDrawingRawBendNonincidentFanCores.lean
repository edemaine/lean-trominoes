/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendPeriodicCores
import LeanTrominoes.PeriodicGridDrawingRawBendFanPlacement

/-! # Digital cores avoid every nonincident fan in every periodic copy -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem fanAt_point_tube {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (factor : Int) (raster : Nat) (center : Cell) (port : GraphPort (Vertex V)) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (fanAt source drawing factor raster center port) point) :
    ((GridSegment.mk center center).scale ((raster : Int)*factor)).RealTubeContains (10*raster) point := by
  have bounds := fanAt_real_bounds source drawing factor raster center port contains
  refine ⟨realCell (Cell.scale ((raster : Int)*factor) center),GridSegment.realContains_start _,?_,?_⟩
  · simp only [realCell,Cell.scale,Int.cast_mul,Int.cast_natCast]
    have near : |point.1-(raster : ℝ)*factor*center.1| ≤ 10*raster := by nlinarith [bounds.1]
    convert near using 1 <;> ring
  · simp only [realCell,Cell.scale,Int.cast_mul,Int.cast_natCast]
    convert bounds.2 using 1 <;> ring

theorem liftedCoreRoute_avoids_nonincident_fan {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (graphLocal : source.IsLocal) (drawingLocal : drawing.IsRealLocal source)
    {tagged : PeriodicEdge (Vertex V) × Nat} (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (copy center : Cell) (port : GraphPort (Vertex V))
    (avoids : ¬((subdivisionSegment source drawing tagged.1).translate (drawing.periodTranslation copy)).RealContains (realCell center))
    {point : ℝ × ℝ} (coreContains : GridPolyline.RealContains (liftedCoreRoute source drawing tagged copy) point) :
    ¬GridPolyline.RealContains (fanAt source drawing (Cubic.coreFactor drawing.gridSize)
      (Cubic.rasterFactor drawing.gridSize) center port) point := by
  intro fanContains
  have bounds := subdivisionSegment_direction_bounds planar.1 graphLocal drawingLocal member
  have translatedBounds :
      |((subdivisionSegment source drawing tagged.1).translate (drawing.periodTranslation copy)).direction.1| ≤ 2*(drawing.gridSize : Int) ∧
      |((subdivisionSegment source drawing tagged.1).translate (drawing.periodTranslation copy)).direction.2| ≤ 2*(drawing.gridSize : Int) := by
    simpa only [GridSegment.direction_translate] using bounds
  have disjoint : ∀ point : ℝ × ℝ,
      ((subdivisionSegment source drawing tagged.1).translate (drawing.periodTranslation copy)).RealContains point →
      ¬(GridSegment.mk center center).RealContains point := by
    intro point contains degenerate
    obtain ⟨t,_,_,x,y⟩ := degenerate
    change point.1 = (center.1 : ℝ)+t*((center.1 : ℝ)-center.1) at x
    change point.2 = (center.2 : ℝ)+t*((center.2 : ℝ)-center.2) at y
    simp only [sub_self,mul_zero,add_zero] at x y
    have equal : point = realCell center := by
      exact Prod.ext x y
    exact avoids (equal ▸ contains)
  have fanTube := (fanAt_point_tube source drawing (Cubic.coreFactor drawing.gridSize)
    (Cubic.rasterFactor drawing.gridSize) center port fanContains).mono
      (show (10 : ℝ)*Cubic.rasterFactor drawing.gridSize ≤ (Cubic.rasterFactor drawing.gridSize : ℝ)*10+3 by nlinarith)
  have gridPositive : (0 : Int) < drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  exact GridSegment.scaled_tubes_disjoint (by omega) (by positivity) (by simpa using cubicScale_tube_spacing drawing)
    translatedBounds (by simp [GridSegment.direction]) disjoint point
    (liftedCoreRoute_tube source drawing tagged copy coreContains) fanTube

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
