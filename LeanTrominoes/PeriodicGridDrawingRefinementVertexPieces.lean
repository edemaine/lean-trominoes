/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.OrthogonalEnlargedGridPoints
import LeanTrominoes.PeriodicGridDrawingRectangleFanOuterContacts

/-! # Rectangle pieces and proper crossing bars avoid scaled graph vertices -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem rectangleEdgePiece?_avoids_scaled_grid_point {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4)
    (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (index column : Nat) (cell anchor : Cell) {piece : EdgeRoutePiece}
    (lookup : rectangleEdgePiece? graph drawing index column cell = some piece)
    (contains : GridPolyline.RealContains piece.route
      (realCell (Cell.scale (paddedRefinementFactor drawing.gridSize) anchor))) : False := by
  obtain ⟨chord,chordMember,image⟩ := rectangleEdgePiece?_raw_source planar.1.1 graphLocal straight index column cell lookup
  have boundary := liftedRectangleInputRoute_column_strip_contact_strip_boundary planar degree graphLocal straight
    chordMember cell ((image _).1.mp contains) anchor.1 (by simp [realCell,Cell.scale])
  have positive : (0 : ℝ) < crossingBound drawing.gridSize := by exact_mod_cast crossingBound_positive drawing
  simp only [realCell,Cell.scale,Int.cast_mul,Int.cast_natCast] at boundary
  rcases boundary with left | right <;> linarith

theorem crossingEdgePiece_avoids_scaled_vertex {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (compatible : drawing.IsCompatible graph) (degree : graph.DegreeAtMost 4)
    (graphLocal : graph.IsLocal)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (straight : (drawing.edgeRoute tagged.2).length = 2)
    (line : Int) (crosses : (drawing.liftedStraightSegment tagged.2 (0,0)).CrossesVerticalLine line)
    {vertex : Cell} (vertexMember : vertex ∈ drawing.vertexPositions) (vertexCell : Cell)
    (contains : GridPolyline.RealContains (crossingEdgePiece graph drawing tagged.2 line).route
      (realCell (Cell.scale (paddedRefinementFactor drawing.gridSize)
        (Cell.add vertex (drawing.periodTranslation vertexCell))))) : False := by
  have spacing : 10*(crossingBound drawing.gridSize : Int) < paddedRefinementFactor drawing.gridSize := by
    simp only [paddedRefinementFactor,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
    have nonnegative : (0 : Int) ≤ crossingBound drawing.gridSize := by positivity
    omega
  have data := enlargedCrossingBar_contains_scaled_grid_point spacing
    ((crossingEdgePiece_raw_image graph drawing tagged.2 line _).mp contains)
  have crossing := periodic_crossing_residue_mem compatible member straight
    (graphLocal _ (List.fst_mem_of_mem_zipIdx member)) (0,0) crosses
  have clearance := paddedPeriodicColumnHeight_avoids_lifted_vertex compatible degree crossing vertexMember vertexCell data.1.symm
  rw [data.2,sub_self,abs_zero] at clearance
  have nonnegative : (0 : Int) ≤ crossingBound drawing.gridSize := by positivity
  omega

end LeanTrominoes.PeriodicGridDrawing
