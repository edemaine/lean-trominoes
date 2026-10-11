/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendContractionDrawing
import LeanTrominoes.PeriodicGridDrawingRawBendContractionLiftedContacts
import LeanTrominoes.PeriodicGridDrawingRawBendPieceVertexContacts
import LeanTrominoes.PeriodicGridDrawingVertexTable

/-! # Joining cubic raw pieces gives a planar drawing of the original graph -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem contractedDrawing_realEdgeRoute {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} {parent : PeriodicEdge V × Nat}
    (member : parent ∈ source.edges.zipIdx) (copy : Cell) :
    (contractedDrawing source drawing).realEdgeRoute parent.2 copy=(contractedRoute source drawing parent).map
      (Cell.add (Cell.scale (cubicScale drawing*drawing.gridSize) copy)) := by
  rw [realEdgeRoute,contractedDrawing_edgeRoute member,contractedDrawing_periodTranslation]

private theorem edge_tagged_of_index {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} {index : Nat}
    (valid : index < (contractedDrawing source drawing).edgeRoutes.length) :
    ∃ edge,(edge,index) ∈ source.edges.zipIdx := by
  have edgeValid : index < source.edges.length := by
    simpa only [contractedDrawing,List.length_map,List.length_zipIdx] using valid
  exact ⟨_,List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem edgeValid)⟩

theorem contractedDrawing_routesMeetOnlyAtEndpoints {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    (degree : source.DegreeAtMost 4) : (contractedDrawing source drawing).RealRoutesMeetOnlyAtEndpoints := by
  intro firstIndex secondIndex firstCopy secondCopy firstValid secondValid different p firstContains secondContains
  obtain ⟨first,firstMember⟩ := edge_tagged_of_index firstValid
  obtain ⟨second,secondMember⟩ := edge_tagged_of_index secondValid
  rw [contractedDrawing_realEdgeRoute firstMember] at firstContains ⊢
  rw [contractedDrawing_realEdgeRoute secondMember] at secondContains ⊢
  exact liftedContractedRoute_contacts planar localDrawing localGraph degree firstMember secondMember
    firstCopy secondCopy different firstContains secondContains

private theorem stored_vertex_lookup {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible source) {point : Cell}
    (member : point ∈ drawing.vertexPositions) :
    ∃ vertex∈source.vertices,drawing.vertexPosition source vertex=point := by
  rw [vertexPositions_eq_map_vertexPosition source drawing compatible.1.1 compatible.2.1] at member
  exact List.mem_map.mp member

theorem contractedDrawing_verticesAvoidRoutes {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    (degree : source.DegreeAtMost 4) : (contractedDrawing source drawing).RealVerticesAvoidRoutes := by
  intro point pointMember vertexCopy edgeCopy edgeIndex edgeValid contains
  obtain ⟨oldPoint,oldPointMember,rfl⟩ := List.mem_map.mp pointMember
  obtain ⟨vertex,vertexMember,positionEq⟩ := stored_vertex_lookup planar.1.1 oldPointMember
  obtain ⟨edge,edgeMember⟩ := edge_tagged_of_index edgeValid
  rw [contractedDrawing_realEdgeRoute edgeMember,contractedDrawing_periodTranslation] at contains ⊢
  have coordinateEq : Cell.add (Cell.scale (cubicFactor drawing) oldPoint)
      (Cell.scale (cubicScale drawing*drawing.gridSize) vertexCopy)=
      Cell.scale (cubicScale drawing) (Cell.add oldPoint (drawing.periodTranslation vertexCopy)) := by
    rw [cubicFactor_cast]
    apply Prod.ext <;> simp only [Cell.scale,Cell.add,periodTranslation] <;> ring
  rw [coordinateEq] at contains ⊢
  obtain ⟨record,recordMember,pieceContains⟩ :=
    liftedContractedRoute_contains planar degree edgeMember edgeCopy contains
  have globalMember := parentRecord_mem edgeMember recordMember
  rw [liftedRefinedPiece_eq] at pieceContains
  have originalMember : Vertex.original vertex ∈ (subdivisionGraph source drawing).vertices :=
    original_vertex_mem.mpr vertexMember
  have contact := liftedPieceRoute_vertex_contact planar localGraph localDrawing originalMember
    (recordIndex_tagged globalMember) (Cell.add (sourceCell drawing record.2.source) edgeCopy) vertexCopy
    (by simpa only [position,positionEq] using pieceContains)
  rw [record_lifted_segment_eq] at contact
  have oldSegmentContains : ((absoluteSegment (position source drawing) drawing.gridSize (sourceCell drawing) record.2).translate
      (drawing.periodTranslation edgeCopy)).RealContains
        (realCell (Cell.add oldPoint (drawing.periodTranslation vertexCopy))) := by
    rcases contact with atStart | atFinish
    · simp only [position,positionEq] at atStart
      rw [atStart]
      exact GridSegment.realContains_start _
    · simp only [position,positionEq] at atFinish
      rw [atFinish]
      exact GridSegment.realContains_finish _
  have pieceMember := record_segment_in_original_route planar.1 globalMember
  have liftedMember := tagged_segment_translate pieceMember (drawing.periodTranslation edgeCopy)
  have oldContains : GridPolyline.RealContains (drawing.realEdgeRoute record.1.1 edgeCopy)
      (realCell (Cell.add oldPoint (drawing.periodTranslation vertexCopy))) :=
    ⟨_,List.fst_mem_of_mem_zipIdx liftedMember,oldSegmentContains⟩
  have oldEndpoint := planar.1.2.2 _ oldPointMember vertexCopy edgeCopy _
    (record_parent_index_valid planar.1.1 globalMember) oldContains
  rw [parentRecord_parent recordMember] at oldEndpoint
  exact liftedContractedRoute_endpoint_transport planar degree edgeMember edgeCopy oldEndpoint

theorem contractedDrawing_planar {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    (degree : source.DegreeAtMost 4) : (contractedDrawing source drawing).IsRealPlanarDrawing source :=
  ⟨⟨contractedDrawing_compatible planar degree,
    contractedDrawing_routesSimple planar localDrawing localGraph degree,
    contractedDrawing_verticesAvoidRoutes planar localDrawing localGraph degree⟩,
    contractedDrawing_routesMeetOnlyAtEndpoints planar localDrawing localGraph degree⟩

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
