/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRectanglePieceLocality
import LeanTrominoes.PeriodicGridDrawingCrossingBarLocality
import LeanTrominoes.PeriodicGridDrawingScaledStraightLocality
import LeanTrominoes.PeriodicGridDrawingRefinementPhysicalImages
import LeanTrominoes.PeriodicGridDrawingRefinementPhysicalSeparation

/-! # The finite straight-edge refinement preserves two-cell locality -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem liftedPaddedIncidenceRoute_in_refined_cell {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    {port : GraphPort Vertex} (member : port ∈ allPorts graph) (cell : Cell) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (liftedPaddedIncidenceRoute graph drawing port cell) point) :
    (straightRefinementDrawing graph drawing).RealPointInCell cell point := by
  have bounds := liftedPaddedIncidenceRoute_in_cell compatible member cell contains
  unfold RealPointInCell
  rw [straightRefinementDrawing_gridSize]
  exact ⟨bounds.1.le,bounds.2.1.le,bounds.2.2.1.le,bounds.2.2.2.le⟩

theorem straightRefinementDrawing_isRealLocal {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2) :
    (straightRefinementDrawing graph drawing).IsRealLocal graph := by
  intro tagged member point contains
  rw [straightRefinementDrawing_edgeRoute member] at contains
  have translated : GridPolyline.RealContains (translatePolyline (Cell.scale (paddedGridSize drawing.gridSize) (0,0))
      (straightRefinementRoute graph drawing tagged)) point := by
    simpa [Cell.scale,translatePolyline_zero] using contains
  have image := straightRefinementRoute_physical_image planar degree graphLocal straight member (0,0) translated
  rcases image with source | target | ⟨column,columnBound,cell,piece,lookup,rectangle⟩ | ⟨line,crosses,bar⟩ | ⟨vertical,core⟩
  · exact Or.inl (liftedPaddedIncidenceRoute_in_refined_cell planar.1.1 (sourcePort_mem_allPorts graph member) (0,0) source)
  · have targetContains : GridPolyline.RealContains (liftedPaddedIncidenceRoute graph drawing (targetPort tagged.1 tagged.2) tagged.1.offset) point := by
      simpa [Cell.add] using target
    exact Or.inr (liftedPaddedIncidenceRoute_in_refined_cell planar.1.1 (targetPort_mem_allPorts graph member) tagged.1.offset targetContains)
  · have pieceContains : GridPolyline.RealContains piece.route point := by
      simpa [Cell.scale,translatePolyline_zero] using rectangle
    exact rectangleEdgePiece?_isRealLocal planar degree graphLocal straight member column columnBound cell lookup pieceContains
  · exact paddedCrossingRoute_isRealLocal planar.1.1 degree graphLocal member (straight _ member) crosses bar
  · have spacing : 20*(crossingBound drawing.gridSize : Int) < paddedRefinementFactor drawing.gridSize := by
      simp only [paddedRefinementFactor,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
      have nonnegative : (0 : Int) ≤ crossingBound drawing.gridSize := by positivity
      omega
    have oldVertical := liftedStraightSegment_isVertical_of_zero planar.1 member (straight _ member) vertical (0,0)
    exact scaled_straight_segment_isRealLocal planar.1.1 graphLocal member
      (GridSegment.verticalCore_realContains_parent oldVertical spacing core)

end LeanTrominoes.PeriodicGridDrawing
