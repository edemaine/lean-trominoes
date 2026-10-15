/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.General.PeriodicOrthocrossingGeneralVertexCoreSeparation
import LeanTrominoes.Graphs.Drawings.Orthogonal.General.PeriodicOrthocrossingGeneralVertexFanSeparation
import LeanTrominoes.Graphs.Drawings.Orthogonal.General.PeriodicOrthocrossingGeneralRealOrthocrossing

/-! # The general routes visit graph vertices only at their own endpoints -/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
attribute [local irreducible] fan core route classifiedCore drawing

theorem drawing_realVerticesAvoidRoutes {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) (orthogonal : Bool)
    (degree : orthogonal = true → graph.DegreeAtMost 4) (isLocal : graph.IsLocal) :
    (drawing graph orthogonal).RealVerticesAvoidRoutes := by
  intro vertex vertexMember vertexCell edgeCell edgeIndex edgeValid contains
  unfold drawing at vertexMember
  change vertex ∈ graph.vertices.zipIdx.map (fun tagged => position graph tagged.2) at vertexMember
  obtain ⟨vertexTagged,vertexTaggedMember,rfl⟩ := List.mem_map.mp vertexMember
  have vertexValid : vertexTagged.2 < graph.vertices.length := List.snd_lt_of_mem_zipIdx vertexTaggedMember
  have edgeBound : edgeIndex < graph.edges.zipIdx.length := by simpa [drawing] using edgeValid
  let edgeTagged := graph.edges.zipIdx[edgeIndex]'edgeBound
  have edgeMember : edgeTagged ∈ graph.edges.zipIdx := List.getElem_mem edgeBound
  have edgeId : edgeTagged.2 = edgeIndex := by simp [edgeTagged,List.getElem_zipIdx]
  have routeEq : (drawing graph orthogonal).realEdgeRoute edgeIndex edgeCell =
      translatePolyline (Cell.scale (drawingGridSize graph : Int) edgeCell)
        (route graph orthogonal edgeTagged.1 edgeTagged.2) := by
    rw [← edgeId]
    exact drawing_realEdgeRoute_of_mem graph orthogonal edgeMember edgeCell
  have vertexEq : Cell.add (position graph vertexTagged.2) ((drawing graph orthogonal).periodTranslation vertexCell) =
      Cell.add (Cell.scale (drawingGridSize graph : Int) vertexCell) (position graph vertexTagged.2) := by
    simp [PeriodicGridDrawing.periodTranslation,drawing_gridSize,Cell.add,add_comm]
  rw [routeEq,vertexEq] at contains ⊢
  have parts := lifted_route_realContains_parts orthogonal degree edgeMember contains
  rcases parts with ⟨target,fanContains⟩ | ⟨piece,pieceMember,coreContains⟩
  · have contact := indexed_vertex_fan_contact wellFormed orthogonal vertexValid
      (routeFanPort_mem graph edgeMember target) fanContains
    rw [contact.1,contact.2]
    exact route_fan_contact_is_endpoint graph orthogonal edgeTagged edgeCell target
  · exact (indexed_vertex_core_disjoint wellFormed vertexValid edgeMember
      (isLocal edgeTagged.1 (List.fst_mem_of_mem_zipIdx edgeMember)) pieceMember vertexCell edgeCell coreContains).elim

end LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
