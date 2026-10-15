/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.GeneralVertexNormalizationDrawing
import LeanTrominoes.Graphs.Drawings.Grid.GeneralVertexNormalizationRouteSimple
import LeanTrominoes.Graphs.Drawings.Grid.GeneralVertexNormalizationVertexAvoidance

/-! # The normalized drawing preserves real planarity -/
namespace LeanTrominoes.GeneralVertexNormalization
open PeriodicOrthocrossing
variable {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}

theorem taggedEdge_at_index {index : Nat} (valid : index < graph.edges.length) :
    ∃ tagged ∈ graph.edges.zipIdx, tagged.2 = index := by
  refine ⟨(graph.edges[index]'valid,index),?_,rfl⟩
  rw [List.mem_zipIdx_iff_getElem?,List.getElem?_eq_getElem valid]

theorem normalizedDrawing_realRoutesAreSimple (valid : drawing.IsRealDrawing graph) (orthogonal : drawing.IsOrthogonal)
    (distinct : DistinctPortSides drawing graph) (chosen : Vertex → GraphPort Vertex) :
    (normalizedDrawing graph drawing chosen).RealRoutesAreSimple := by
  intro route member
  obtain ⟨tagged,taggedMember,rfl⟩ := List.mem_map.mp member
  exact normalizedRoute_simple valid orthogonal distinct chosen taggedMember (0,0)

theorem normalizedDrawing_orthogonal (valid : drawing.IsRealDrawing graph) (orthogonal : drawing.IsOrthogonal)
    (distinct : DistinctPortSides drawing graph) (chosen : Vertex → GraphPort Vertex) :
    (normalizedDrawing graph drawing chosen).IsOrthogonal := by
  apply (PeriodicGridDrawing.isOrthogonal_iff_routes _).mpr
  intro route member
  obtain ⟨tagged,taggedMember,rfl⟩ := List.mem_map.mp member
  exact normalizedRoute_orthogonal valid orthogonal distinct chosen taggedMember (0,0)

theorem normalizedDrawing_realVerticesAvoidRoutes (valid : drawing.IsRealDrawing graph) (orthogonal : drawing.IsOrthogonal)
    (distinct : DistinctPortSides drawing graph) (chosen : Vertex → GraphPort Vertex) :
    (normalizedDrawing graph drawing chosen).RealVerticesAvoidRoutes := by
  intro vertex member vertexCell edgeCell index indexValid contains
  obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
  have indexBound : index < graph.edges.length := by simpa [normalizedDrawing] using indexValid
  obtain ⟨tagged,taggedMember,rfl⟩ := taggedEdge_at_index indexBound
  rw [normalizedDrawing_realEdgeRoute chosen taggedMember,normalizedDrawing_periodTranslation,
    ← Cell.scale_add] at contains ⊢
  exact normalizedRoute_vertexAvoidance valid orthogonal distinct chosen taggedMember originalMember vertexCell edgeCell contains

theorem normalizedDrawing_isRealDrawing (valid : drawing.IsRealDrawing graph) (orthogonal : drawing.IsOrthogonal)
    (distinct : DistinctPortSides drawing graph) (chosen : Vertex → GraphPort Vertex) :
    (normalizedDrawing graph drawing chosen).IsRealDrawing graph :=
  ⟨normalizedDrawing_compatible valid.1 chosen,normalizedDrawing_realRoutesAreSimple valid orthogonal distinct chosen,
    normalizedDrawing_realVerticesAvoidRoutes valid orthogonal distinct chosen⟩

theorem normalizedDrawing_isRealPlanarDrawing (planar : drawing.IsRealPlanarDrawing graph) (orthogonal : drawing.IsOrthogonal)
    (chosen : Vertex → GraphPort Vertex) : (normalizedDrawing graph drawing chosen).IsRealPlanarDrawing graph := by
  have distinct := distinctPortSides_of_planar_orthogonal planar orthogonal
  refine ⟨normalizedDrawing_isRealDrawing planar.1 orthogonal distinct chosen,?_⟩
  intro firstIndex secondIndex firstCell secondCell firstValid secondValid different point firstContains secondContains
  have firstBound : firstIndex < graph.edges.length := by simpa [normalizedDrawing] using firstValid
  have secondBound : secondIndex < graph.edges.length := by simpa [normalizedDrawing] using secondValid
  obtain ⟨a,am,rfl⟩ := taggedEdge_at_index firstBound
  obtain ⟨b,bm,rfl⟩ := taggedEdge_at_index secondBound
  rw [normalizedDrawing_realEdgeRoute chosen am] at firstContains ⊢
  rw [normalizedDrawing_realEdgeRoute chosen bm] at secondContains ⊢
  exact normalized_route_occurrences_contacts planar orthogonal distinct chosen am bm firstCell secondCell different firstContains secondContains

end LeanTrominoes.GeneralVertexNormalization
