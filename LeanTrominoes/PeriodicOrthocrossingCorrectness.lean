/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingConstruction
import Mathlib.Tactic.NormNum

/-!
# Basic correctness of the periodic track construction

This file proves the finite-presentation part of Theorem 2.1's construction:
the generated vertex positions are distinct and lie inside the fundamental
square, every generated route is retrieved at the same index as its
protoedge, and its endpoints are exactly the source and translated target
positions.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

theorem getD_map_zipIdx_of_mem {α β : Type*}
    (values : List α) (function : α × Nat → β)
    (default : β) {tagged : α × Nat}
    (taggedMem : tagged ∈ values.zipIdx) :
    (values.zipIdx.map function).getD tagged.2 default =
      function tagged := by
  have indexLt : tagged.2 < (values.zipIdx.map function).length := by
    simp only [List.length_map, List.length_zipIdx]
    simpa using List.snd_lt_of_mem_zipIdx taggedMem
  rw [List.getD_eq_getElem _ _ indexLt]
  simp only [List.getElem_map]
  have zipIndexLt : tagged.2 < values.zipIdx.length := by
    simpa using List.snd_lt_of_mem_zipIdx taggedMem
  have taggedAt :
      values.zipIdx[tagged.2]'zipIndexLt = tagged := by
    apply Prod.ext
    · simpa using (List.mem_zipIdx' taggedMem).2.symm
    · simp
  rw [taggedAt]

theorem vertexPosition_injective :
    Function.Injective vertexPosition := by
  intro first second equal
  have xEqual := congrArg Prod.fst equal
  simp only [vertexPosition, vertexX] at xEqual
  omega

/-- Constructed vertex positions are pairwise distinct. -/
theorem constructedVertexPositions_nodup {Vertex : Type*}
    (graph : PeriodicGraph Vertex) :
    (constructedVertexPositions graph).Nodup := by
  have indicesNodup :=
    List.nodup_zipIdx_map_snd graph.vertices
  have mapped := indicesNodup.map vertexPosition_injective
  rw [List.map_map] at mapped
  unfold constructedVertexPositions
  change (graph.vertices.zipIdx.map
    (vertexPosition ∘ Prod.snd)).Nodup
  exact mapped

theorem drawing_vertexPositions_nodup {Vertex : Type*}
    [DecidableEq Vertex] (graph : PeriodicGraph Vertex) :
    (drawing graph).vertexPositions.Nodup :=
  constructedVertexPositions_nodup graph

/-- Indexed lookup in the generated position list recovers the closed-form
position assigned to that protovertex. -/
theorem drawing_vertexPosition_of_mem {Vertex : Type*}
    [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    {vertex : Vertex} (vertexMem : vertex ∈ graph.vertices) :
    (drawing graph).vertexPosition graph vertex =
      vertexPosition (graph.vertices.idxOf vertex) := by
  have indexLt : graph.vertices.idxOf vertex < graph.vertices.length :=
    List.idxOf_lt_length_iff.mpr vertexMem
  have vertexAt :
      graph.vertices[graph.vertices.idxOf vertex] = vertex :=
    List.idxOf_get indexLt
  have taggedMem :
      (vertex, graph.vertices.idxOf vertex) ∈ graph.vertices.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff]
    exact ⟨indexLt, vertexAt⟩
  unfold PeriodicGridDrawing.vertexPosition drawing
  exact getD_map_zipIdx_of_mem graph.vertices
    (fun tagged : Vertex × Nat => vertexPosition tagged.2)
    (0, 0) taggedMem

/-- Every generated vertex lies in the open scaled fundamental square. -/
theorem drawing_positions_in_fundamental_square {Vertex : Type*}
    [DecidableEq Vertex] (graph : PeriodicGraph Vertex) :
    ∀ position ∈ (drawing graph).vertexPositions,
      (drawing graph).PositionInFundamentalSquare position := by
  intro position positionMem
  simp only [drawing, constructedVertexPositions, List.mem_map] at positionMem
  rcases positionMem with ⟨tagged, taggedMem, rfl⟩
  have indexLt : tagged.2 < graph.vertices.length := by
    simpa using List.snd_lt_of_mem_zipIdx taggedMem
  unfold PeriodicGridDrawing.PositionInFundamentalSquare
  rw [drawing_gridSize]
  simp only [vertexPosition, vertexX]
  have sizePositive := drawingGridSize_pos graph
  unfold drawingGridSize at sizePositive ⊢
  norm_num
  omega

/-- Indexed lookup in the generated route list recovers the route built for
that protoedge. -/
theorem drawing_edgeRoute_of_mem {Vertex : Type*}
    [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    {taggedEdge : PeriodicEdge Vertex × Nat}
    (edgeMem : taggedEdge ∈ graph.edges.zipIdx) :
    (drawing graph).edgeRoute taggedEdge.2 =
      constructedEdgeRoute graph taggedEdge.1 taggedEdge.2 := by
  unfold PeriodicGridDrawing.edgeRoute drawing constructedEdgeRoutes
  exact getD_map_zipIdx_of_mem graph.edges
    (fun tagged : PeriodicEdge Vertex × Nat =>
      constructedEdgeRoute graph tagged.1 tagged.2)
    [] edgeMem

/-- Every route has the source and translated target endpoints prescribed by
its protoedge. -/
theorem drawing_routesMatch {Vertex : Type*}
    [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) :
    (drawing graph).RoutesMatch graph := by
  intro taggedEdge edgeMem
  have endpoints :=
    wellFormed.2 taggedEdge.1
      (List.fst_mem_of_mem_zipIdx edgeMem)
  rw [drawing_edgeRoute_of_mem graph edgeMem,
    constructedEdgeRoute_head?, constructedEdgeRoute_getLast?]
  constructor
  · rw [drawing_vertexPosition_of_mem graph endpoints.1]
  · rw [drawing_vertexPosition_of_mem graph endpoints.2]
    rw [show (drawing graph).periodTranslation taggedEdge.1.offset =
      Cell.scale (drawingGridSize graph : Int) taggedEdge.1.offset by
        simp [PeriodicGridDrawing.periodTranslation]]

/-- The generated finite presentation is compatible with the graph. -/
theorem drawing_isCompatible {Vertex : Type*}
    [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) :
    (drawing graph).IsCompatible graph := by
  exact ⟨wellFormed, drawing_vertexPositions_length graph,
    drawing_edgeRoutes_length graph, drawing_vertexPositions_nodup graph,
    drawing_positions_in_fundamental_square graph,
    drawing_routesMatch wellFormed⟩

end PeriodicOrthocrossing
end LeanTrominoes
