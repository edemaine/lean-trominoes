/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRefinementVertexPieces
import LeanTrominoes.PeriodicGridDrawingNonverticalEdgeRouteSimple

/-! # Nonvertical replacement routes meet scaled vertices only at endpoints -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem nonverticalEdgeRoute_vertex_avoidance {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4)
    (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (nonvertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 ≠
      (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1)
    {vertex : Cell} (vertexMember : vertex ∈ drawing.vertexPositions) (vertexCell : Cell)
    (contains : GridPolyline.RealContains (nonverticalEdgeRoute graph drawing tagged)
      (realCell (Cell.scale (paddedRefinementFactor drawing.gridSize)
        (Cell.add vertex (drawing.periodTranslation vertexCell))))) :
    GridPolyline.RealIsEndpoint (nonverticalEdgeRoute graph drawing tagged)
      (realCell (Cell.scale (paddedRefinementFactor drawing.gridSize)
        (Cell.add vertex (drawing.periodTranslation vertexCell)))) := by
  have ends := (nonverticalEdgeRoute_endpoints planar degree graphLocal straight member nonvertical).2
  obtain ⟨piece,pieceMember,pieceContains⟩ :=
    (nonverticalEdgeRoute_valid planar degree graphLocal straight member nonvertical).2.2 _ |>.mp contains
  simp only [nonverticalEdgePieces,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at pieceMember
  rcases pieceMember with ((source | rectangle) | crossing) | target
  · subst piece
    have raw := (sourceEdgePiece_lifted_image graph drawing tagged _).mp pieceContains
    have spacing : 20*(crossingBound drawing.gridSize : Int) < paddedRefinementFactor drawing.gridSize := by
      simp only [paddedRefinementFactor,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
      have nonnegative : (0 : Int) ≤ crossingBound drawing.gridSize := by positivity
      omega
    have positionEq := enlargedRectangleTemplate_contains_scaled_grid_point spacing _ _ raw
    have sourceEq : drawing.vertexPosition graph tagged.1.source =
        Cell.add vertex (drawing.periodTranslation vertexCell) := by
      simpa [sourcePort,liftedPaddedIncidenceRoute,Cell.add,periodTranslation,Cell.scale] using positionEq
    exact Or.inl ⟨_,ends.1,congrArg (fun position => realCell (Cell.scale (paddedRefinementFactor drawing.gridSize) position)) sourceEq.symm⟩
  · obtain ⟨column,_,rectangleMember⟩ := List.mem_flatMap.mp rectangle
    obtain ⟨cell,_,lookup⟩ := List.mem_filterMap.mp rectangleMember
    exact (rectangleEdgePiece?_avoids_scaled_grid_point planar degree graphLocal straight tagged.2 column cell _ lookup pieceContains).elim
  · obtain ⟨line,_,lookup⟩ := List.mem_filterMap.mp crossing
    split_ifs at lookup with crosses
    have equal := Option.some.inj lookup
    subst piece
    exact (crossingEdgePiece_avoids_scaled_vertex planar.1.1 degree graphLocal member (straight _ member)
      line crosses vertexMember vertexCell pieceContains).elim
  · subst piece
    have raw := (GridPolyline.realContains_reverse _ _).mp pieceContains
    have spacing : 20*(crossingBound drawing.gridSize : Int) < paddedRefinementFactor drawing.gridSize := by
      simp only [paddedRefinementFactor,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
      have nonnegative : (0 : Int) ≤ crossingBound drawing.gridSize := by positivity
      omega
    have positionEq := enlargedRectangleTemplate_contains_scaled_grid_point spacing _ _ raw
    have targetEq : Cell.add (drawing.vertexPosition graph tagged.1.target) (drawing.periodTranslation tagged.1.offset) =
        Cell.add vertex (drawing.periodTranslation vertexCell) := positionEq
    refine Or.inr ⟨_,ends.2,?_⟩
    have pointEq := congrArg (fun position => realCell (Cell.scale (paddedRefinementFactor drawing.gridSize) position)) targetEq.symm
    simpa [realCell,Cell.scale,Cell.add,periodTranslation,paddedGridSize,mul_add,add_comm,mul_assoc] using pointEq

end LeanTrominoes.PeriodicGridDrawing
