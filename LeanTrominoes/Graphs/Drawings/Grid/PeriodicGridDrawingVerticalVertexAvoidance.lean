/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingVerticalEdgeRoute
import LeanTrominoes.Common.Geometry.GridPolylineRealEndpointAffine

/-! # Directly scaled routes preserve avoidance of every lifted graph vertex -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem verticalEdgeRoute_vertex_avoidance {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (valid : drawing.IsRealDrawing graph)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    {vertex : Cell} (vertexMember : vertex ∈ drawing.vertexPositions) (vertexCell : Cell)
    (contains : GridPolyline.RealContains (verticalEdgeRoute drawing tagged.2)
      (realCell (Cell.scale (paddedRefinementFactor drawing.gridSize)
        (Cell.add vertex (drawing.periodTranslation vertexCell))))) :
    GridPolyline.RealIsEndpoint (verticalEdgeRoute drawing tagged.2)
      (realCell (Cell.scale (paddedRefinementFactor drawing.gridSize)
        (Cell.add vertex (drawing.periodTranslation vertexCell)))) := by
  have nonzero : (paddedRefinementFactor drawing.gridSize : Int) ≠ 0 := by
    exact_mod_cast (paddedRefinementFactor_positive drawing.gridSize).ne'
  have oldContains : GridPolyline.RealContains (drawing.edgeRoute tagged.2)
      (realCell (Cell.add vertex (drawing.periodTranslation vertexCell))) := by
    apply (GridPolyline.realContains_scale _ nonzero _).mp
    simpa only [verticalEdgeRoute,realCell,Cell.scale,Int.cast_mul,Int.cast_natCast] using contains
  have indexValid : tagged.2 < drawing.edgeRoutes.length := by
    rw [valid.1.2.2.1]
    exact List.snd_lt_of_mem_zipIdx member
  have routeZero : drawing.realEdgeRoute tagged.2 (0,0) = drawing.edgeRoute tagged.2 := by
    change translatePolyline (drawing.periodTranslation (0,0)) (drawing.edgeRoute tagged.2) = _
    simp [periodTranslation,Cell.scale,translatePolyline_zero]
  have oldEndpoint := valid.2.2 vertex vertexMember vertexCell (0,0) tagged.2 indexValid
    (by rw [routeZero]; exact oldContains)
  rw [routeZero] at oldEndpoint
  have scaledEndpoint := oldEndpoint.scale (paddedRefinementFactor drawing.gridSize)
  simpa [verticalEdgeRoute,realEdgeRoute,periodTranslation,Cell.scale,Cell.add,realCell] using scaledEndpoint

end LeanTrominoes.PeriodicGridDrawing
