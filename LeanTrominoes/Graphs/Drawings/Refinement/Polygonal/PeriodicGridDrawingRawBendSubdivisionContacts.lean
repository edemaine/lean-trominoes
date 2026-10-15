/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingRawBendSubdivisionRecords
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingPolygonalListedPointContacts
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingBendSubdivisionRouteSimplicity

/-! # Real contact guarantees for the unperturbed bend subdivision

Every raw edge occurrence is exactly an original polygonal piece occurrence.
Original planarity therefore supplies simplicity, endpoint-only contacts,
and vertex avoidance, including bends on fundamental-cell boundaries.
-/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision PeriodicOrthocrossing

def subdivisionSegment {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (edge : PeriodicEdge (Vertex V)) : GridSegment :=
  ⟨position source drawing edge.source,Cell.add (position source drawing edge.target) (Cell.scale drawing.gridSize edge.offset)⟩

theorem subdivision_edgeRoute_of_tagged {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) {tagged : PeriodicEdge (Vertex V) × Nat}
    (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx) :
    (subdivisionDrawing source drawing).edgeRoute tagged.2 = straightRoute source drawing tagged.1 := by
  have valid : tagged.2 < (subdivisionGraph source drawing).edges.length := by
    simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx member
  have lookup := (List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp member)).2
  unfold edgeRoute
  change ((subdivisionGraph source drawing).edges.map (straightRoute source drawing)).getD tagged.2 [] = _
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using valid),List.getElem_map,lookup]

theorem subdivision_segment_image {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    {tagged : PeriodicEdge (Vertex V) × Nat} (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (translate : Cell) (point : ℝ × ℝ) :
    GridPolyline.RealContains ((subdivisionDrawing source drawing).realEdgeRoute tagged.2 translate) point ↔
      ((subdivisionSegment source drawing tagged.1).translate (drawing.periodTranslation translate)).RealContains point := by
  simp only [realEdgeRoute,subdivision_edgeRoute_of_tagged source drawing member,straightRoute,List.map_cons,List.map_nil,
    GridPolyline.RealContains,gridPolylineSegments,List.mem_singleton,exists_eq_left]
  rfl

theorem subdivision_segment_endpoints {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    {tagged : PeriodicEdge (Vertex V) × Nat} (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (translate : Cell) (point : ℝ × ℝ) :
    GridPolyline.RealIsEndpoint ((subdivisionDrawing source drawing).realEdgeRoute tagged.2 translate) point ↔
      point = realCell ((subdivisionSegment source drawing tagged.1).translate (drawing.periodTranslation translate)).start ∨
        point = realCell ((subdivisionSegment source drawing tagged.1).translate (drawing.periodTranslation translate)).finish := by
  simp only [realEdgeRoute,subdivision_edgeRoute_of_tagged source drawing member,straightRoute,List.map_cons,List.map_nil,
    GridPolyline.RealIsEndpoint,List.head?_cons,List.getLast?_cons_cons,List.getLast?_singleton,Option.some.injEq,
    subdivisionSegment,GridSegment.translate,exists_eq_left']
  rfl

theorem lifted_subdivision_segment_eq {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (edge : PeriodicEdge (Vertex V)) (translate : Cell) :
    (subdivisionSegment source drawing edge).translate (drawing.periodTranslation translate) =
      (absoluteSegment (position source drawing) drawing.gridSize (sourceCell drawing) edge).translate
        (drawing.periodTranslation (Cell.sub translate (sourceCell drawing edge.source))) := by
  unfold subdivisionSegment absoluteSegment GridSegment.translate
  congr 1 <;> apply Prod.ext <;> simp only [periodTranslation,Cell.add,Cell.sub,Cell.scale] <;> ring

theorem subdivision_segment_contacts {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) {first second : PeriodicEdge (Vertex V) × Nat}
    (firstMember : first ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (secondMember : second ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (firstCell secondCell : Cell) (different : (first.2,firstCell) ≠ (second.2,secondCell)) :
    GridSegment.EndpointContacts ((subdivisionSegment source drawing first.1).translate (drawing.periodTranslation firstCell))
      ((subdivisionSegment source drawing second.1).translate (drawing.periodTranslation secondCell)) := by
  have firstRecord := recordAt_mem (by simpa using List.snd_lt_of_mem_zipIdx firstMember)
  have secondRecord := recordAt_mem (by simpa using List.snd_lt_of_mem_zipIdx secondMember)
  have firstPiece := record_segment_in_original_route planar.1 firstRecord
  have secondPiece := record_segment_in_original_route planar.1 secondRecord
  rw [recordAt_edge firstMember] at firstPiece
  rw [recordAt_edge secondMember] at secondPiece
  have contacts := polygonal_segment_contacts planar
    (BendSubdivision.edgeRoute_tagged_mem_of_lt (record_parent_index_valid planar.1.1 firstRecord))
    (BendSubdivision.edgeRoute_tagged_mem_of_lt (record_parent_index_valid planar.1.1 secondRecord)) firstPiece secondPiece
    (Cell.sub firstCell (sourceCell drawing first.1.source)) (Cell.sub secondCell (sourceCell drawing second.1.source))
    (lifted_record_keys_ne firstMember secondMember firstCell secondCell different)
  simpa only [← lifted_subdivision_segment_eq source drawing] using contacts

theorem subdivision_edge_tagged_of_route_index {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    {index : Nat} (valid : index < (subdivisionDrawing source drawing).edgeRoutes.length) :
    ∃ edge, (edge,index) ∈ (subdivisionGraph source drawing).edges.zipIdx := by
  have edgeValid : index < (subdivisionGraph source drawing).edges.length := by
    simpa only [subdivisionDrawing,List.length_map] using valid
  exact ⟨_,List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem edgeValid)⟩

theorem subdivision_routesMeetOnlyAtEndpoints {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) : (subdivisionDrawing source drawing).RealRoutesMeetOnlyAtEndpoints := by
  intro firstIndex secondIndex firstCell secondCell firstValid secondValid different point firstContains secondContains
  obtain ⟨first,firstMember⟩ := subdivision_edge_tagged_of_route_index firstValid
  obtain ⟨second,secondMember⟩ := subdivision_edge_tagged_of_route_index secondValid
  rw [subdivision_segment_image source drawing firstMember] at firstContains
  rw [subdivision_segment_image source drawing secondMember] at secondContains
  have endpoints := subdivision_segment_contacts planar firstMember secondMember firstCell secondCell different point firstContains secondContains
  rw [subdivision_segment_endpoints source drawing firstMember,subdivision_segment_endpoints source drawing secondMember]
  exact endpoints

theorem subdivision_segment_nonconstant {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) {tagged : PeriodicEdge (Vertex V) × Nat}
    (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx) :
    (subdivisionSegment source drawing tagged.1).start ≠ (subdivisionSegment source drawing tagged.1).finish := by
  have recordMember := recordAt_mem (by simpa using List.snd_lt_of_mem_zipIdx member)
  have pieceMember := record_segment_in_original_route planar.1 recordMember
  rw [recordAt_edge member] at pieceMember
  have routeMember := List.fst_mem_of_mem_zipIdx
    (BendSubdivision.edgeRoute_tagged_mem_of_lt (record_parent_index_valid planar.1.1 recordMember))
  have nonconstant := (planar.1.2.1 _ routeMember).2.1 _ (List.fst_mem_of_mem_zipIdx pieceMember)
  have segmentEq := straightRoute_absolute_segment source drawing tagged.1
  change (subdivisionSegment source drawing tagged.1).translate (Cell.scale drawing.gridSize (sourceCell drawing tagged.1.source)) = _ at segmentEq
  intro equal
  apply nonconstant
  rw [← segmentEq]
  exact congrArg (Cell.add (Cell.scale drawing.gridSize (sourceCell drawing tagged.1.source))) equal

theorem subdivision_routesSimple {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) : (subdivisionDrawing source drawing).RealRoutesAreSimple := by
  intro route member
  obtain ⟨edge,edgeMember,rfl⟩ := List.mem_map.mp member
  obtain ⟨index,indexValid,indexMember⟩ := List.mem_iff_getElem.mp edgeMember
  have taggedMember : (edge,index) ∈ (subdivisionGraph source drawing).edges.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    exact List.getElem?_eq_some_iff.mpr ⟨indexValid,indexMember⟩
  exact GridPolyline.isRealSimple_pair (subdivision_segment_nonconstant planar taggedMember)

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
