/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendSubdivisionContacts

/-! # Raw subdivision vertices avoid nonincident real edge interiors -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision PeriodicOrthocrossing

theorem bend_lifted_position_copy {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) {edgeIndex pointIndex : Nat}
    (valid : pointIndex+1 < (drawing.edgeRoute edgeIndex).length) (translate : Cell) :
    Cell.add (drawing.periodTranslation (Cell.sub translate (sourceCell (V := V) drawing (.bend edgeIndex pointIndex))))
      (drawing.edgeRoute edgeIndex)[pointIndex] =
      Cell.add (position source drawing (.bend edgeIndex pointIndex)) (drawing.periodTranslation translate) := by
  have pointValid : pointIndex < (drawing.edgeRoute edgeIndex).length := by omega
  simp only [sourceCell,position,List.getD_eq_getElem _ _ pointValid,periodTranslation,cell,representative,Cell.add,Cell.sub,Cell.scale]
  apply Prod.ext <;> dsimp
  · nlinarith [Int.emod_add_mul_ediv ((drawing.edgeRoute edgeIndex)[pointIndex]).1 (drawing.gridSize : Int)]
  · nlinarith [Int.emod_add_mul_ediv ((drawing.edgeRoute edgeIndex)[pointIndex]).2 (drawing.gridSize : Int)]

theorem subdivision_verticesAvoidRoutes {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) : (subdivisionDrawing source drawing).RealVerticesAvoidRoutes := by
  intro vertex vertexMember vertexCell edgeCell edgeIndex edgeValid contains
  obtain ⟨id,idMember,rfl⟩ := List.mem_map.mp vertexMember
  obtain ⟨edge,edgeMember⟩ := subdivision_edge_tagged_of_route_index edgeValid
  have recordMember := recordAt_mem (by simpa using List.snd_lt_of_mem_zipIdx edgeMember)
  have pieceMember := record_segment_in_original_route planar.1 recordMember
  rw [recordAt_edge edgeMember] at pieceMember
  have parentValid := record_parent_index_valid planar.1.1 recordMember
  rw [subdivision_segment_image source drawing edgeMember] at contains
  rw [subdivision_segment_endpoints source drawing edgeMember]
  rw [lifted_subdivision_segment_eq source drawing] at contains ⊢
  have periods (cell : Cell) : (subdivisionDrawing source drawing).periodTranslation cell = drawing.periodTranslation cell := rfl
  simp only [periods] at contains ⊢
  let copy := Cell.sub edgeCell (sourceCell drawing edge.source)
  have liftedMember := tagged_segment_translate pieceMember (drawing.periodTranslation copy)
  cases id with
  | original oldVertex =>
      have oldVertexMember := planar.1.1.vertexPosition_mem (original_vertex_mem.mp idMember)
      have routeContains : GridPolyline.RealContains (drawing.realEdgeRoute (recordAt source drawing edgeIndex).1.1 copy)
          (realCell (Cell.add (drawing.vertexPosition source oldVertex) (drawing.periodTranslation vertexCell))) :=
        ⟨_,by simpa only [realEdgeRoute,translatePolyline] using List.fst_mem_of_mem_zipIdx liftedMember,contains⟩
      have endpoint := planar.1.2.2 _ oldVertexMember vertexCell copy _ parentValid routeContains
      have simple := (planar.1.2.1 _ (List.fst_mem_of_mem_zipIdx (BendSubdivision.edgeRoute_tagged_mem_of_lt parentValid))).translate
        (drawing.periodTranslation copy)
      exact simple.endpoint_segment_contact liftedMember endpoint contains
  | bend oldEdge oldPoint =>
      have bounds := bend_vertex_mem_bounds planar.1.1 idMember
      change ((absoluteSegment (position source drawing) drawing.gridSize (sourceCell drawing) edge).translate
        (drawing.periodTranslation copy)).RealContains
          (realCell (Cell.add (position source drawing (.bend oldEdge oldPoint)) (drawing.periodTranslation vertexCell))) at contains
      rw [← bend_lifted_position_copy source drawing bounds.2.2 vertexCell] at contains ⊢
      exact polygonal_listed_point_segment_contact planar bounds.1 parentValid bounds.2.2 pieceMember
        (Cell.sub vertexCell (sourceCell (V := V) drawing (.bend oldEdge oldPoint))) copy contains

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
