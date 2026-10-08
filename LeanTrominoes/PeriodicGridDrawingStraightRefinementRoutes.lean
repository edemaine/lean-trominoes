/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingVerticalEdgeRoute
import LeanTrominoes.PeriodicGridDrawingNonverticalEdgeRouteSimple

/-! # Replacement routes for all straight protoedges -/
namespace LeanTrominoes.PeriodicGridDrawing
open PeriodicOrthocrossing OrthogonalDrawingRefinement

def straightRefinementRoute {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge Vertex × Nat) : List Cell :=
  if (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 =
      (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1 then
    verticalEdgeRoute drawing tagged.2
  else nonverticalEdgeRoute graph drawing tagged

theorem straightRefinementRoute_valid {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4)
    (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) :
    GridPolyline.IsRealOpenSimple (straightRefinementRoute graph drawing tagged) ∧
      OrthogonalPolyline (straightRefinementRoute graph drawing tagged) := by
  unfold straightRefinementRoute
  split_ifs with vertical
  · exact ⟨verticalEdgeRoute_isRealOpenSimple planar.1 member (straight tagged member),
      verticalEdgeRoute_orthogonal planar.1 member (straight tagged member) vertical⟩
  · have valid := nonverticalEdgeRoute_valid planar degree graphLocal straight member vertical
    exact ⟨valid.1,valid.2.1⟩

theorem straightRefinementRoute_endpoints {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4)
    (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) :
    (straightRefinementRoute graph drawing tagged).head? =
      some (Cell.scale (paddedRefinementFactor drawing.gridSize)
        (drawing.vertexPosition graph tagged.1.source)) ∧
    (straightRefinementRoute graph drawing tagged).getLast? =
      some (Cell.add (Cell.scale (paddedGridSize drawing.gridSize) tagged.1.offset)
        (Cell.scale (paddedRefinementFactor drawing.gridSize)
          (drawing.vertexPosition graph tagged.1.target))) := by
  unfold straightRefinementRoute
  split_ifs with vertical
  · exact verticalEdgeRoute_endpoints planar.1.1 member
  · exact (nonverticalEdgeRoute_endpoints planar degree graphLocal straight member vertical).2

end LeanTrominoes.PeriodicGridDrawing
