/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridPolylineRealSegmentContacts
import LeanTrominoes.Common.Geometry.GridPolylineRealAffineSimplicity

/-! # Endpoint-only contacts between lifted polygonal segment occurrences -/
namespace LeanTrominoes.PeriodicGridDrawing
open PeriodicOrthocrossing

theorem realEdgeRoute_of_tagged_route {drawing : PeriodicGridDrawing}
    {tagged : List Cell × Nat} (member : tagged∈drawing.edgeRoutes.zipIdx) (translate : Cell) :
    drawing.realEdgeRoute tagged.2 translate=translatePolyline (drawing.periodTranslation translate) tagged.1 := by
  have lookup := List.mem_zipIdx_iff_getElem?.mp member
  have value : drawing.edgeRoute tagged.2=tagged.1 := by
    unfold edgeRoute
    rw [List.getD_eq_getElem _ _ (List.snd_lt_of_mem_zipIdx member)]
    exact (List.getElem?_eq_some_iff.mp lookup).2
  simp only [realEdgeRoute,value,translatePolyline]

theorem tagged_segment_translate {route : List Cell} {tagged : GridSegment × Nat}
    (member : tagged∈(gridPolylineSegments route).zipIdx) (offset : Cell) :
    (tagged.1.translate offset,tagged.2)∈(gridPolylineSegments (translatePolyline offset route)).zipIdx := by
  rw [gridPolylineSegments_translatePolyline,List.zipIdx_map]
  exact List.mem_map.mpr ⟨tagged,member,rfl⟩

theorem polygonal_segment_contacts {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph)
    {firstRoute secondRoute : List Cell × Nat}
    (firstRouteMember : firstRoute∈drawing.edgeRoutes.zipIdx)
    (secondRouteMember : secondRoute∈drawing.edgeRoutes.zipIdx)
    {first second : GridSegment × Nat}
    (firstMember : first∈(gridPolylineSegments firstRoute.1).zipIdx)
    (secondMember : second∈(gridPolylineSegments secondRoute.1).zipIdx)
    (firstCell secondCell : Cell)
    (different : (firstRoute.2,first.2,firstCell)≠(secondRoute.2,second.2,secondCell)) :
    GridSegment.EndpointContacts (first.1.translate (drawing.periodTranslation firstCell))
      (second.1.translate (drawing.periodTranslation secondCell)) := by
  have firstSimple := (planar.1.2.1 firstRoute.1 (List.fst_mem_of_mem_zipIdx firstRouteMember)).translate
    (drawing.periodTranslation firstCell)
  have secondSimple := (planar.1.2.1 secondRoute.1 (List.fst_mem_of_mem_zipIdx secondRouteMember)).translate
    (drawing.periodTranslation secondCell)
  have firstLifted := tagged_segment_translate firstMember (drawing.periodTranslation firstCell)
  have secondLifted := tagged_segment_translate secondMember (drawing.periodTranslation secondCell)
  by_cases same : (firstRoute.2,firstCell)=(secondRoute.2,secondCell)
  · have indexEq : firstRoute.2=secondRoute.2 := congrArg Prod.fst same
    have cellEq : firstCell=secondCell := congrArg Prod.snd same
    have routeEq : firstRoute.1=secondRoute.1 := by
      have firstAt := List.mem_zipIdx_iff_getElem?.mp firstRouteMember
      have secondAt := List.mem_zipIdx_iff_getElem?.mp secondRouteMember
      rw [indexEq,secondAt] at firstAt
      exact (Option.some.inj firstAt).symm
    have segmentDifferent : first.2≠second.2 := by
      intro equal
      exact different (by simp only [indexEq,cellEq,equal])
    rw [← cellEq] at secondLifted ⊢
    rw [← routeEq] at secondLifted
    exact firstSimple.segment_contacts firstLifted secondLifted segmentDifferent
  · intro p firstContains secondContains
    have endpoints := planar.2 firstRoute.2 secondRoute.2 firstCell secondCell
      (List.snd_lt_of_mem_zipIdx firstRouteMember) (List.snd_lt_of_mem_zipIdx secondRouteMember) same p
      (by rw [realEdgeRoute_of_tagged_route firstRouteMember]; exact ⟨_,List.fst_mem_of_mem_zipIdx firstLifted,firstContains⟩)
      (by rw [realEdgeRoute_of_tagged_route secondRouteMember]; exact ⟨_,List.fst_mem_of_mem_zipIdx secondLifted,secondContains⟩)
    rw [realEdgeRoute_of_tagged_route firstRouteMember,realEdgeRoute_of_tagged_route secondRouteMember] at endpoints
    exact ⟨firstSimple.endpoint_segment_contact firstLifted endpoints.1 firstContains,
      secondSimple.endpoint_segment_contact secondLifted endpoints.2 secondContains⟩

end LeanTrominoes.PeriodicGridDrawing
