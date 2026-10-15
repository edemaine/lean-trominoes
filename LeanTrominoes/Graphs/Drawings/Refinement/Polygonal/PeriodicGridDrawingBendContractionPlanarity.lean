/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingBendContractionDrawing
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingBendContractionLiftedContacts

/-! # Joining the subdivision restores a planar drawing of the original graph -/
namespace LeanTrominoes.PeriodicGridDrawing.BendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement

theorem contractedDrawing_realEdgeRoute {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} {parent : PeriodicEdge V × Nat}
    (member : parent ∈ source.edges.zipIdx) (copy : Cell) :
    (contractedDrawing source drawing).realEdgeRoute parent.2 copy=(contractedRoute source drawing parent).map
      (Cell.add ((orthogonalSubdivision source drawing).periodTranslation copy)) := by
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
  obtain ⟨index,valid,atIndex⟩ := List.mem_iff_getElem.mp member
  have graphValid : index < source.vertices.length := by rwa [compatible.2.1] at valid
  let vertex := source.vertices[index]'graphValid
  have vertexMember : vertex ∈ source.vertices := List.getElem_mem graphValid
  have indexValid := List.idxOf_lt_length_of_mem vertexMember
  have indexEq : source.vertices.idxOf vertex=index :=
    compatible.1.1.getElem_inj_iff.mp (List.getElem_idxOf indexValid)
  refine ⟨vertex,vertexMember,?_⟩
  rw [vertexPosition,indexEq,List.getD_eq_getElem _ _ valid]
  exact atIndex

theorem original_scaled_vertex_mem {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    (degree : source.DegreeAtMost 4) {point : Cell} (member : point ∈ drawing.vertexPositions) :
    Cell.scale (polygonalScale drawing) point ∈ (orthogonalSubdivision source drawing).vertexPositions := by
  obtain ⟨vertex,vertexMember,positionEq⟩ := stored_vertex_lookup planar.1.1 member
  have listed : Vertex.original vertex ∈ (subdivisionGraph source drawing (bendRefinementFactor drawing)).vertices :=
    original_vertex_mem.mpr vertexMember
  have outputPlanar := orthogonalSubdivision_planar planar localDrawing localGraph degree
  have outputMember := outputPlanar.1.1.vertexPosition_mem listed
  rw [orthogonalSubdivision_vertexPosition listed,position,positionEq,Cell.scale_scale,← Nat.cast_mul] at outputMember
  exact outputMember

theorem contractedDrawing_verticesAvoidRoutes {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    (degree : source.DegreeAtMost 4) : (contractedDrawing source drawing).RealVerticesAvoidRoutes := by
  intro point pointMember vertexCopy edgeCopy edgeIndex edgeValid contains
  obtain ⟨oldPoint,oldPointMember,rfl⟩ := List.mem_map.mp pointMember
  obtain ⟨edge,edgeMember⟩ := edge_tagged_of_index edgeValid
  rw [contractedDrawing_realEdgeRoute edgeMember,contractedDrawing_periodTranslation] at contains ⊢
  obtain ⟨record,recordMember,pieceContains⟩ :=
    liftedContractedRoute_contains planar localDrawing localGraph degree edgeMember edgeCopy contains
  have globalMember := parentRecord_mem edgeMember recordMember
  have outputPlanar := orthogonalSubdivision_planar planar localDrawing localGraph degree
  rw [liftedRefinedPiece_eq] at pieceContains
  have pieceValid : recordIndex source drawing (bendRefinementFactor drawing) record <
      (orthogonalSubdivision source drawing).edgeRoutes.length := by
    simpa only [orthogonalSubdivision,straightRefinementDrawing,List.length_map,List.length_zipIdx] using recordIndex_valid globalMember
  have endpoint := outputPlanar.1.2.2 _
    (original_scaled_vertex_mem planar localDrawing localGraph degree oldPointMember) vertexCopy _ _ pieceValid pieceContains
  rw [← liftedRefinedPiece_eq source drawing record edgeCopy] at endpoint
  obtain ⟨a,oldContains,pointEq⟩ := liftedRefinedPiece_endpoint_preimage planar localDrawing localGraph degree globalMember edgeCopy endpoint
  have coordinateEq : Cell.add (Cell.scale (polygonalScale drawing) oldPoint)
      ((orthogonalSubdivision source drawing).periodTranslation vertexCopy)=
      Cell.scale (subdivisionScale drawing) (Cell.add (Cell.scale (bendRefinementFactor drawing) oldPoint)
        ((InteriorBends.perturbDrawing drawing (bendRefinementFactor drawing)).periodTranslation vertexCopy)) := by
    rw [Cell.scale_add,Cell.scale_scale,← Nat.cast_mul,subdivision_period_scaled]
    rfl
  have scalePositive : (0:Int) < subdivisionScale drawing := by
    exact_mod_cast paddedRefinementFactor_positive (bendRefinementFactor drawing*drawing.gridSize)
  have oldPointEq : Cell.add (Cell.scale (bendRefinementFactor drawing) oldPoint)
      ((InteriorBends.perturbDrawing drawing (bendRefinementFactor drawing)).periodTranslation vertexCopy)=a := by
    apply Cell.scale_injective scalePositive.ne'
    apply realCell_injective
    simpa only [coordinateEq] using pointEq
  rw [← oldPointEq] at oldContains
  have movedPlanar := InteriorBends.perturbDrawing_planar planar localDrawing localGraph (bendRefinementFactor_spacing drawing)
  have movedMember : Cell.scale (bendRefinementFactor drawing) oldPoint ∈
      (InteriorBends.perturbDrawing drawing (bendRefinementFactor drawing)).vertexPositions :=
    List.mem_map.mpr ⟨oldPoint,oldPointMember,rfl⟩
  have oldEndpoint := movedPlanar.1.2.2 _ movedMember vertexCopy edgeCopy _
    (record_parent_index_valid planar.1.1 globalMember) oldContains
  rw [parentRecord_parent recordMember] at oldEndpoint
  rw [pointEq,← oldPointEq]
  exact liftedContractedRoute_endpoint_transport planar localDrawing localGraph degree edgeMember edgeCopy oldEndpoint

theorem contractedDrawing_planar {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    (degree : source.DegreeAtMost 4) : (contractedDrawing source drawing).IsRealPlanarDrawing source :=
  ⟨⟨contractedDrawing_compatible planar localDrawing localGraph degree,
    contractedDrawing_routesSimple planar localDrawing localGraph degree,
    contractedDrawing_verticesAvoidRoutes planar localDrawing localGraph degree⟩,
    contractedDrawing_routesMeetOnlyAtEndpoints planar localDrawing localGraph degree⟩

end LeanTrominoes.PeriodicGridDrawing.BendSubdivision
