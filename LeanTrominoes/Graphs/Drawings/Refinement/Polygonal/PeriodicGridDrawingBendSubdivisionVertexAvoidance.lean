/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingBendSubdivisionRouteSimplicity
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingBendSubdivisionVertexTransport
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingPolygonalListedPointContacts

/-! # Original and inserted vertices avoid subdivision edge interiors -/
namespace LeanTrominoes.PeriodicGridDrawing.BendSubdivision
open PeriodicGraph.BendSubdivision PeriodicOrthocrossing

theorem subdivisionDrawing_verticesAvoidRoutes {V : Type*} [DecidableEq V]
    {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (localDrawing : drawing.IsRealLocal source)
    (localGraph : source.IsLocal) {factor : Nat}
    (spacing : 16*(drawing.gridSize:Int)+8 < (factor:Int)) :
    (subdivisionDrawing source drawing factor).RealVerticesAvoidRoutes := by
  intro vertex vertexMember vertexCell edgeCell edgeIndex edgeValid contains
  have gridPositive : (0:Int) < drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have positive : 0 < factor := by omega
  obtain ⟨id,idMember,rfl⟩ := List.mem_map.mp vertexMember
  obtain ⟨edge,edgeMember⟩ := subdivision_edge_tagged_of_route_index edgeValid
  have recordMember := recordAt_mem (by simpa using List.snd_lt_of_mem_zipIdx edgeMember)
  have pieceMember := record_segment_in_moved_route planar recordMember
  rw [recordAt_edge edgeMember] at pieceMember
  have parentValid := record_parent_index_valid planar.1.1 recordMember
  have movedPlanar := InteriorBends.perturbDrawing_planar planar localDrawing localGraph spacing
  rw [subdivision_segment_image source drawing factor edgeMember] at contains
  rw [subdivision_segment_endpoints source drawing factor edgeMember]
  rw [lifted_subdivision_segment_eq source drawing positive] at contains ⊢
  let copy := Cell.sub edgeCell (sourceCell drawing factor edge.source)
  have liftedMember := tagged_segment_translate pieceMember
    ((InteriorBends.perturbDrawing drawing factor).periodTranslation copy)
  cases id with
  | original oldVertex =>
      rw [← original_lifted_representative source drawing positive] at contains ⊢
      have oldVertexMember := planar.1.1.vertexPosition_mem (original_vertex_mem.mp idMember)
      have movedVertexMember : Cell.scale factor (drawing.vertexPosition source oldVertex) ∈
          (InteriorBends.perturbDrawing drawing factor).vertexPositions := List.mem_map.mpr ⟨_,oldVertexMember,rfl⟩
      have routeContains : GridPolyline.RealContains
          ((InteriorBends.perturbDrawing drawing factor).realEdgeRoute
            (recordAt source drawing factor edgeIndex).1.1 copy)
          (realCell (Cell.add (Cell.scale factor (drawing.vertexPosition source oldVertex))
            ((InteriorBends.perturbDrawing drawing factor).periodTranslation vertexCell))) :=
        ⟨_,by simpa only [realEdgeRoute,translatePolyline] using List.fst_mem_of_mem_zipIdx liftedMember,contains⟩
      have endpoint := movedPlanar.1.2.2 _ movedVertexMember vertexCell copy _ parentValid routeContains
      have simple := (movedPlanar.1.2.1 _
        (List.fst_mem_of_mem_zipIdx (edgeRoute_tagged_mem_of_lt parentValid))).translate
          ((InteriorBends.perturbDrawing drawing factor).periodTranslation copy)
      exact simple.endpoint_segment_contact liftedMember endpoint contains
  | bend oldEdge oldPoint =>
      have bounds := bend_vertex_mem_bounds planar.1.1 idMember
      have pointValid : oldPoint+1 < ((InteriorBends.perturbDrawing drawing factor).edgeRoute oldEdge).length :=
        by simpa only [moved_route_length] using bounds.2.2
      have indexValid : oldEdge < (InteriorBends.perturbDrawing drawing factor).edgeRoutes.length := by
        simpa only [InteriorBends.perturbDrawing,List.length_map] using bounds.1
      rw [← bend_lifted_representative_copy source drawing positive bounds.2.2 vertexCell] at contains ⊢
      exact polygonal_listed_point_segment_contact movedPlanar indexValid parentValid pointValid pieceMember
        (Cell.sub vertexCell (sourceCell (V := V) drawing factor (.bend oldEdge oldPoint))) copy contains

end LeanTrominoes.PeriodicGridDrawing.BendSubdivision
