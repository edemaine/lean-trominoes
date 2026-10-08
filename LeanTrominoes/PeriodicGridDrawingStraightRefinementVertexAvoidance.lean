/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingStraightRefinementDrawing
import LeanTrominoes.PeriodicGridDrawingNonverticalVertexAvoidance
import LeanTrominoes.PeriodicGridDrawingVerticalVertexAvoidance

/-! # The assembled drawing avoids graph vertices in every periodic copy -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem straightRefinementRoute_vertex_avoidance {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4)
    (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    {vertex : Cell} (vertexMember : vertex ∈ drawing.vertexPositions) (vertexCell : Cell)
    (contains : GridPolyline.RealContains (straightRefinementRoute graph drawing tagged)
      (realCell (Cell.scale (paddedRefinementFactor drawing.gridSize)
        (Cell.add vertex (drawing.periodTranslation vertexCell))))) :
    GridPolyline.RealIsEndpoint (straightRefinementRoute graph drawing tagged)
      (realCell (Cell.scale (paddedRefinementFactor drawing.gridSize)
        (Cell.add vertex (drawing.periodTranslation vertexCell)))) := by
  unfold straightRefinementRoute at contains ⊢
  split_ifs at contains ⊢ with vertical
  · exact verticalEdgeRoute_vertex_avoidance planar.1 member vertexMember vertexCell contains
  · exact nonverticalEdgeRoute_vertex_avoidance planar degree graphLocal straight member vertical vertexMember vertexCell contains

theorem straightRefinementDrawing_vertices_avoid_routes {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4)
    (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2) :
    (straightRefinementDrawing graph drawing).RealVerticesAvoidRoutes := by
  intro vertex member vertexCell edgeCell index indexValid contains
  obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
  have indexBound : index < graph.edges.length := by simpa [straightRefinementDrawing] using indexValid
  let tagged : PeriodicEdge Vertex × Nat := (graph.edges[index]'indexBound,index)
  have taggedMember : tagged ∈ graph.edges.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?,List.getElem?_eq_getElem indexBound]
  change GridPolyline.RealContains (translatePolyline
    ((straightRefinementDrawing graph drawing).periodTranslation edgeCell)
    ((straightRefinementDrawing graph drawing).edgeRoute index)) _ at contains
  rw [straightRefinementDrawing_edgeRoute taggedMember,periodTranslation,straightRefinementDrawing_gridSize] at contains
  have relativeContains := (GridPolyline.realContains_translate_inverse _ _ _).mp contains
  let relativeCell := Cell.add vertexCell (Cell.scale (-1) edgeCell)
  have pointEq :
      ((realCell (Cell.add (Cell.scale (paddedRefinementFactor drawing.gridSize) original)
        ((straightRefinementDrawing graph drawing).periodTranslation vertexCell))).1 -
          (Cell.scale (paddedGridSize drawing.gridSize) edgeCell).1,
       (realCell (Cell.add (Cell.scale (paddedRefinementFactor drawing.gridSize) original)
        ((straightRefinementDrawing graph drawing).periodTranslation vertexCell))).2 -
          (Cell.scale (paddedGridSize drawing.gridSize) edgeCell).2) =
        realCell (Cell.scale (paddedRefinementFactor drawing.gridSize)
          (Cell.add original (drawing.periodTranslation relativeCell))) := by
    rw [periodTranslation,straightRefinementDrawing_gridSize]
    apply Prod.ext <;> simp [relativeCell,realCell,Cell.add,Cell.scale,periodTranslation,paddedGridSize] <;> ring
  rw [pointEq] at relativeContains
  have relativeEndpoint := straightRefinementRoute_vertex_avoidance planar degree graphLocal straight taggedMember
    originalMember relativeCell relativeContains
  have shifted := relativeEndpoint.translate (Cell.scale (paddedGridSize drawing.gridSize) edgeCell)
  rw [← pointEq] at shifted
  have shiftedPoint :
      ((Cell.scale (paddedGridSize drawing.gridSize) edgeCell).1 +
        ((realCell (Cell.add (Cell.scale (paddedRefinementFactor drawing.gridSize) original)
          ((straightRefinementDrawing graph drawing).periodTranslation vertexCell))).1 -
            (Cell.scale (paddedGridSize drawing.gridSize) edgeCell).1),
       (Cell.scale (paddedGridSize drawing.gridSize) edgeCell).2 +
        ((realCell (Cell.add (Cell.scale (paddedRefinementFactor drawing.gridSize) original)
          ((straightRefinementDrawing graph drawing).periodTranslation vertexCell))).2 -
            (Cell.scale (paddedGridSize drawing.gridSize) edgeCell).2)) =
      realCell (Cell.add (Cell.scale (paddedRefinementFactor drawing.gridSize) original)
        ((straightRefinementDrawing graph drawing).periodTranslation vertexCell)) := by
    apply Prod.ext <;> simp
  rw [shiftedPoint] at shifted
  change GridPolyline.RealIsEndpoint (translatePolyline
    ((straightRefinementDrawing graph drawing).periodTranslation edgeCell)
    ((straightRefinementDrawing graph drawing).edgeRoute index)) _
  rw [straightRefinementDrawing_edgeRoute taggedMember,periodTranslation,straightRefinementDrawing_gridSize]
  exact shifted

theorem straightRefinementDrawing_isRealDrawing {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4)
    (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2) :
    (straightRefinementDrawing graph drawing).IsRealDrawing graph :=
  ⟨straightRefinementDrawing_compatible planar degree graphLocal straight,
    straightRefinementDrawing_routes_simple planar degree graphLocal straight,
    straightRefinementDrawing_vertices_avoid_routes planar degree graphLocal straight⟩

end LeanTrominoes.PeriodicGridDrawing
