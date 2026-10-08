/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRefinementPhysicalSeparation
import LeanTrominoes.PeriodicGridDrawingStraightRefinementVertexAvoidance

/-! # The executable straight-edge refinement is planar in every periodic copy -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem straightRefinementDrawing_routes_meet_only_at_endpoints {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2) :
    (straightRefinementDrawing graph drawing).RealRoutesMeetOnlyAtEndpoints := by
  intro firstIndex lastIndex firstCell lastCell firstValid lastValid different point firstContains lastContains
  have firstBound : firstIndex < graph.edges.length := by simpa [straightRefinementDrawing] using firstValid
  have lastBound : lastIndex < graph.edges.length := by simpa [straightRefinementDrawing] using lastValid
  let first : PeriodicEdge Vertex × Nat := (graph.edges[firstIndex]'firstBound,firstIndex)
  let last : PeriodicEdge Vertex × Nat := (graph.edges[lastIndex]'lastBound,lastIndex)
  have firstMember : first ∈ graph.edges.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?,List.getElem?_eq_getElem firstBound]
  have lastMember : last ∈ graph.edges.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?,List.getElem?_eq_getElem lastBound]
  have firstRaw : GridPolyline.RealContains (translatePolyline (Cell.scale (paddedGridSize drawing.gridSize) firstCell)
      (straightRefinementRoute graph drawing first)) point := by
    change GridPolyline.RealContains (translatePolyline _ ((straightRefinementDrawing graph drawing).edgeRoute firstIndex)) point at firstContains
    rw [straightRefinementDrawing_edgeRoute firstMember,periodTranslation,straightRefinementDrawing_gridSize] at firstContains
    exact firstContains
  have lastRaw : GridPolyline.RealContains (translatePolyline (Cell.scale (paddedGridSize drawing.gridSize) lastCell)
      (straightRefinementRoute graph drawing last)) point := by
    change GridPolyline.RealContains (translatePolyline _ ((straightRefinementDrawing graph drawing).edgeRoute lastIndex)) point at lastContains
    rw [straightRefinementDrawing_edgeRoute lastMember,periodTranslation,straightRefinementDrawing_gridSize] at lastContains
    exact lastContains
  obtain ⟨vertex,vertexMember,vertexCell,pointEq⟩ := refinementPhysicalContains_contact_scaled_vertex planar degree graphLocal straight
    firstMember lastMember firstCell lastCell different
    (straightRefinementRoute_physical_image planar degree graphLocal straight firstMember firstCell firstRaw)
    (straightRefinementRoute_physical_image planar degree graphLocal straight lastMember lastCell lastRaw)
  have newVertexMember : Cell.scale (paddedRefinementFactor drawing.gridSize) vertex ∈
      (straightRefinementDrawing graph drawing).vertexPositions :=
    List.mem_map.mpr ⟨vertex,vertexMember,rfl⟩
  have pointNew : point = realCell (Cell.add (Cell.scale (paddedRefinementFactor drawing.gridSize) vertex)
      ((straightRefinementDrawing graph drawing).periodTranslation vertexCell)) := by
    rw [pointEq]
    simp only [periodTranslation,straightRefinementDrawing_gridSize]
    apply congrArg realCell
    apply Prod.ext <;> simp [Cell.add,Cell.scale,paddedGridSize] <;> ring
  have avoids := straightRefinementDrawing_vertices_avoid_routes planar degree graphLocal straight
  rw [pointNew] at firstContains lastContains ⊢
  exact ⟨avoids _ newVertexMember vertexCell firstCell firstIndex firstValid firstContains,
    avoids _ newVertexMember vertexCell lastCell lastIndex lastValid lastContains⟩

theorem straightRefinementDrawing_isRealPlanarDrawing {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2) :
    (straightRefinementDrawing graph drawing).IsRealPlanarDrawing graph :=
  ⟨straightRefinementDrawing_isRealDrawing planar degree graphLocal straight,
    straightRefinementDrawing_routes_meet_only_at_endpoints planar degree graphLocal straight⟩

end LeanTrominoes.PeriodicGridDrawing
