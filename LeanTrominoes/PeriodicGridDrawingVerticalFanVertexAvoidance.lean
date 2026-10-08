/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingVerticalFanRouteSimple
import LeanTrominoes.PeriodicGridDrawingVerticalVertexAvoidance
import LeanTrominoes.OrthogonalEnlargedGridPoints

/-! # Vertical fan routes meet lifted graph vertices only at graph endpoints -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem verticalFanEdgeRoute_vertex_avoidance {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (vertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 =
      (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1)
    {vertex : Cell} (vertexMember : vertex ∈ drawing.vertexPositions) (vertexCell : Cell)
    (contains : GridPolyline.RealContains (verticalFanEdgeRoute graph drawing tagged)
      (realCell (Cell.scale (paddedRefinementFactor drawing.gridSize)
        (Cell.add vertex (drawing.periodTranslation vertexCell))))) :
    GridPolyline.RealIsEndpoint (verticalFanEdgeRoute graph drawing tagged)
      (realCell (Cell.scale (paddedRefinementFactor drawing.gridSize)
        (Cell.add vertex (drawing.periodTranslation vertexCell)))) := by
  have ends := (verticalFanEdgeRoute_endpoints graph drawing tagged).2
  have spacing : 20*(crossingBound drawing.gridSize : Int) < paddedRefinementFactor drawing.gridSize := by
    simp only [paddedRefinementFactor,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
    have nonnegative : (0 : Int) ≤ crossingBound drawing.gridSize := by positivity
    omega
  obtain ⟨piece,pieceMember,pieceContains⟩ :=
    (verticalFanEdgeRoute_valid planar degree straight member vertical).2.2 _ |>.mp contains
  simp only [verticalFanRouteWord,List.mem_cons,List.not_mem_nil,or_false] at pieceMember
  rcases pieceMember with rfl | rfl | rfl
  · have positionEq := enlargedRectangleTemplate_contains_scaled_grid_point spacing _ _ pieceContains
    have sourceEq : drawing.vertexPosition graph tagged.1.source =
        Cell.add vertex (drawing.periodTranslation vertexCell) := positionEq
    exact Or.inl ⟨_,ends.1,congrArg (fun position => realCell (Cell.scale (paddedRefinementFactor drawing.gridSize) position)) sourceEq.symm⟩
  · have scaledContains := (verticalCoreRoute_valid planar degree straight member vertical).2.2 _ pieceContains
    have oldRouteEq : drawing.edgeRoute tagged.2 =
        [(drawing.straightSegment tagged.2).start,(drawing.straightSegment tagged.2).finish] := by
      obtain ⟨first,last,routeEq⟩ := List.length_eq_two.mp (straight _ member)
      simp [straightSegment,routeEq]
    have directContains : GridPolyline.RealContains (verticalEdgeRoute drawing tagged.2)
        (realCell (Cell.scale (paddedRefinementFactor drawing.gridSize)
          (Cell.add vertex (drawing.periodTranslation vertexCell)))) := by
      simpa [verticalEdgeRoute,oldRouteEq,scalePolyline,GridPolyline.RealContains,gridPolylineSegments,GridSegment.scale] using scaledContains
    have endpoint := verticalEdgeRoute_vertex_avoidance planar.1 member vertexMember vertexCell directContains
    have directEnds := verticalEdgeRoute_endpoints planar.1.1 member
    rcases endpoint with ⟨value,head,pointEq⟩ | ⟨value,last,pointEq⟩
    · exact Or.inl ⟨value,ends.1.trans (directEnds.1.symm.trans head),pointEq⟩
    · exact Or.inr ⟨value,ends.2.trans (directEnds.2.symm.trans last),pointEq⟩
  · have raw := (GridPolyline.realContains_reverse _ _).mp pieceContains
    have positionEq := enlargedRectangleTemplate_contains_scaled_grid_point spacing _ _ raw
    have targetEq : Cell.add (drawing.vertexPosition graph tagged.1.target) (drawing.periodTranslation tagged.1.offset) =
        Cell.add vertex (drawing.periodTranslation vertexCell) := positionEq
    refine Or.inr ⟨_,ends.2,?_⟩
    have pointEq := congrArg (fun position => realCell (Cell.scale (paddedRefinementFactor drawing.gridSize) position)) targetEq.symm
    simpa [realCell,Cell.scale,Cell.add,periodTranslation,paddedGridSize,mul_add,add_comm,mul_assoc] using pointEq

end LeanTrominoes.PeriodicGridDrawing
