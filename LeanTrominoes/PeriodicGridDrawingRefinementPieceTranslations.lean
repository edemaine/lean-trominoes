/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingVerticalCoreRouteGeometry

/-! # The fan and vertical-core pieces commute with every periodic shift -/
namespace LeanTrominoes.GridSegment

theorem verticalCore_translate (segment : GridSegment) (offset : Cell) (factor : Int) (radius : Nat) :
    (segment.translate offset).verticalCore factor radius =
      (segment.verticalCore factor radius).translate (Cell.scale factor offset) := by
  simp only [verticalCore,translate,Cell.add]
  apply congrArg₂ GridSegment.mk
  all_goals apply Prod.ext <;> simp [Cell.scale] <;> ring

end LeanTrominoes.GridSegment
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem liftedPaddedIncidenceRoute_add_cell {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (port : GraphPort Vertex) (cell shift : Cell) :
    liftedPaddedIncidenceRoute graph drawing port (Cell.add cell shift) =
      translatePolyline (Cell.scale (paddedGridSize drawing.gridSize) shift)
        (liftedPaddedIncidenceRoute graph drawing port cell) := by
  simp only [liftedPaddedIncidenceRoute,enlargedRectangleTemplate,translatePolyline,List.map_map]
  apply List.map_congr_left
  intro point _
  apply Prod.ext <;> simp [Cell.add,Cell.scale,periodTranslation,paddedGridSize] <;> ring

theorem verticalCoreRoute_lifted_image {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (vertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 =
      (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1)
    (cell : Cell) (point : ℝ × ℝ) :
    GridPolyline.RealContains (translatePolyline (Cell.scale (paddedGridSize drawing.gridSize) cell)
      (verticalCoreRoute graph drawing tagged)) point ↔
      ((drawing.liftedStraightSegment tagged.2 cell).verticalCore (paddedRefinementFactor drawing.gridSize)
        (crossingBound drawing.gridSize)).RealContains point := by
  rw [verticalCoreRoute_eq_segment planar degree straight member vertical]
  unfold liftedStraightSegment
  rw [GridSegment.verticalCore_translate]
  have offsetEq : Cell.scale (paddedRefinementFactor drawing.gridSize) (drawing.periodTranslation cell) =
      Cell.scale (paddedGridSize drawing.gridSize) cell := by
    apply Prod.ext <;> simp [periodTranslation,Cell.scale,paddedGridSize] <;> ring
  rw [offsetEq]
  simp [translatePolyline,GridPolyline.RealContains,gridPolylineSegments,GridSegment.translate]

end LeanTrominoes.PeriodicGridDrawing
