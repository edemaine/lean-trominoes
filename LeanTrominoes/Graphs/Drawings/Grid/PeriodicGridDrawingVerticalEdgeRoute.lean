/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingCrossingPieceWindow
import LeanTrominoes.Common.Geometry.GridPolylineRealAffineSimplicity

/-! # Straight vertical edges use their directly scaled segment -/
namespace LeanTrominoes.PeriodicGridDrawing
open PeriodicOrthocrossing OrthogonalDrawingRefinement

def verticalEdgeRoute (drawing : PeriodicGridDrawing) (index : Nat) : List Cell :=
  scalePolyline (paddedRefinementFactor drawing.gridSize) (drawing.edgeRoute index)

theorem verticalEdgeRoute_endpoints {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) :
    (verticalEdgeRoute drawing tagged.2).head? =
      some (Cell.scale (paddedRefinementFactor drawing.gridSize) (drawing.vertexPosition graph tagged.1.source)) ∧
    (verticalEdgeRoute drawing tagged.2).getLast? =
      some (Cell.add (Cell.scale (paddedGridSize drawing.gridSize) tagged.1.offset)
        (Cell.scale (paddedRefinementFactor drawing.gridSize) (drawing.vertexPosition graph tagged.1.target))) := by
  have ends := compatible.2.2.2.2.2 tagged member
  simp only [verticalEdgeRoute,scalePolyline,List.head?_map,List.getLast?_map,ends.1,ends.2,Option.map_some]
  refine ⟨trivial,?_⟩
  apply congrArg some
  apply Prod.ext <;> simp [Cell.add,Cell.scale,periodTranslation,paddedGridSize] <;> ring

theorem verticalEdgeRoute_isRealOpenSimple {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (valid : drawing.IsRealDrawing graph)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (straight : (drawing.edgeRoute tagged.2).length = 2) :
    GridPolyline.IsRealOpenSimple (verticalEdgeRoute drawing tagged.2) := by
  obtain ⟨first,last,routeEq⟩ := List.length_eq_two.mp straight
  have nondegenerate := straightSegment_nondegenerate valid member straight
  have unequal : first ≠ last := by simpa [straightSegment,routeEq] using nondegenerate
  have positive : (0 : Int) < paddedRefinementFactor drawing.gridSize := by exact_mod_cast paddedRefinementFactor_positive drawing.gridSize
  apply GridPolyline.isRealOpenSimple_of_box_certificate
  simp [verticalEdgeRoute,routeEq,scalePolyline,GridPolyline.SimpleBoxCertificate,gridPolylineSegments]
  exact (Cell.scale_injective positive.ne').ne unequal

theorem verticalEdgeRoute_orthogonal {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (valid : drawing.IsRealDrawing graph)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (straight : (drawing.edgeRoute tagged.2).length = 2)
    (vertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 =
      (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1) :
    OrthogonalPolyline (verticalEdgeRoute drawing tagged.2) := by
  obtain ⟨first,last,routeEq⟩ := List.length_eq_two.mp straight
  have nondegenerate := straightSegment_nondegenerate valid member straight
  have unequal : first ≠ last := by simpa [straightSegment,routeEq] using nondegenerate
  have sameX : first.1 = last.1 := by
    simpa [liftedStraightSegment,straightSegment,routeEq,GridSegment.translate,Cell.add] using vertical
  have differentY : first.2 ≠ last.2 := fun equal => unequal (Prod.ext sameX equal)
  have positive : (0 : Int) < paddedRefinementFactor drawing.gridSize := by exact_mod_cast paddedRefinementFactor_positive drawing.gridSize
  simp [verticalEdgeRoute,routeEq,scalePolyline,OrthogonalPolyline,GridSegment.IsAxisAligned,GridSegment.IsVertical,GridSegment.IsHorizontal,Cell.scale,sameX]
  exact ⟨differentY, Nat.ne_of_gt (paddedRefinementFactor_positive drawing.gridSize)⟩

end LeanTrominoes.PeriodicGridDrawing
