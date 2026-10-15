/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawing

/-! # Dense numeric names preserve a periodic drawing -/
namespace LeanTrominoes
namespace PeriodicGraph

def indexedEdge {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (edge : PeriodicEdge Vertex) : PeriodicEdge Nat :=
  ⟨graph.vertices.idxOf edge.source, graph.vertices.idxOf edge.target, edge.offset⟩

def indexed {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) : PeriodicGraph Nat :=
  ⟨List.range graph.vertices.length, graph.edges.map graph.indexedEdge⟩

theorem indexed_wellFormed {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} (wellFormed : graph.IsWellFormed) : graph.indexed.IsWellFormed := by
  refine ⟨List.nodup_range, ?_⟩
  intro edge member
  obtain ⟨old,oldMember,rfl⟩ := List.mem_map.mp member
  have ends := wellFormed.2 old oldMember
  exact ⟨List.mem_range.mpr (List.idxOf_lt_length_iff.mpr ends.1),
    List.mem_range.mpr (List.idxOf_lt_length_iff.mpr ends.2)⟩

theorem indexed_isLocal {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} (graphLocal : graph.IsLocal) : graph.indexed.IsLocal := by
  intro edge member
  obtain ⟨old,oldMember,rfl⟩ := List.mem_map.mp member
  exact graphLocal old oldMember

end PeriodicGraph
namespace PeriodicGridDrawing

theorem vertexPosition_indexed {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) {vertex : Vertex}
    (member : vertex ∈ graph.vertices) :
    drawing.vertexPosition graph.indexed (graph.vertices.idxOf vertex) =
      drawing.vertexPosition graph vertex := by
  simp only [vertexPosition,PeriodicGraph.indexed]
  have bound := List.idxOf_lt_length_iff.mpr member
  have indexEq := (List.nodup_range (n := graph.vertices.length)).idxOf_getElem
    (graph.vertices.idxOf vertex) (by simpa using bound)
  simpa only [List.getElem_range] using congrArg
    (fun index => drawing.vertexPositions.getD index (0,0)) indexEq

theorem isCompatible_indexed {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (compatible : drawing.IsCompatible graph) : drawing.IsCompatible graph.indexed := by
  refine ⟨graph.indexed_wellFormed compatible.1, ?_, ?_, compatible.2.2.2.1,
    compatible.2.2.2.2.1, ?_⟩
  · simpa only [PeriodicGraph.indexed,List.length_range] using compatible.2.1
  · simpa only [PeriodicGraph.indexed,List.length_map] using compatible.2.2.1
  · intro tagged member
    change tagged ∈ (graph.edges.map graph.indexedEdge).zipIdx at member
    rw [List.zipIdx_map] at member
    obtain ⟨old,oldMember,taggedEq⟩ := List.mem_map.mp member
    subst tagged
    have ends := compatible.1.2 old.1 (List.fst_mem_of_mem_zipIdx oldMember)
    simpa only [Prod.map, id, PeriodicGraph.indexedEdge,
      vertexPosition_indexed graph drawing ends.1,
      vertexPosition_indexed graph drawing ends.2] using compatible.2.2.2.2.2 old oldMember

end PeriodicGridDrawing
end LeanTrominoes
