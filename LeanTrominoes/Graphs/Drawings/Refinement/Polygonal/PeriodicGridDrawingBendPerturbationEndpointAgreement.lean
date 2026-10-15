/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingBendPerturbationSegmentTransport
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRealEndpointVertices
import LeanTrominoes.Common.Geometry.GridPolylineRealAffineSimplicity
import LeanTrominoes.Common.Geometry.GridPolylinePerturbationSimplicity

/-! # Shared endpoints in distinct periodic routes have identical moved coordinates -/
namespace LeanTrominoes.PeriodicGridDrawing.InteriorBends
open PeriodicOrthocrossing

theorem edgeRoute_mem_of_lt {drawing : PeriodicGridDrawing} {index : Nat}
    (valid : index<drawing.edgeRoutes.length) : drawing.edgeRoute index∈drawing.edgeRoutes := by
  unfold edgeRoute
  rw [List.getD_eq_getElem _ _ valid]
  exact List.getElem_mem valid

theorem translated_oriented_start (segment : GridSegment) (offset : Cell) (backwards : Bool) :
    ((segment.translate offset).oriented backwards).start=Cell.add offset (segment.oriented backwards).start := by
  cases backwards <;> rfl

theorem lifted_endpoint_contacts {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    {firstIndex secondIndex : Nat} (firstValid : firstIndex<drawing.edgeRoutes.length)
    (secondValid : secondIndex<drawing.edgeRoutes.length) (firstCell secondCell : Cell)
    (different : (firstIndex,firstCell)≠(secondIndex,secondCell))
    {first second : GridSegment} (firstMember : first∈gridPolylineSegments (drawing.edgeRoute firstIndex))
    (secondMember : second∈gridPolylineSegments (drawing.edgeRoute secondIndex)) :
    GridSegment.EndpointContacts (first.translate (drawing.periodTranslation firstCell))
      (second.translate (drawing.periodTranslation secondCell)) := by
  intro p firstContains secondContains
  have endpoints := planar.2 firstIndex secondIndex firstCell secondCell firstValid secondValid different p
    (lifted_segment_in_route firstMember firstContains) (lifted_segment_in_route secondMember secondContains)
  have firstSimple := (planar.1.2.1 _ (edgeRoute_mem_of_lt firstValid)).translate (drawing.periodTranslation firstCell)
  have secondSimple := (planar.1.2.1 _ (edgeRoute_mem_of_lt secondValid)).translate (drawing.periodTranslation secondCell)
  have firstLifted : first.translate (drawing.periodTranslation firstCell)∈
      gridPolylineSegments (drawing.realEdgeRoute firstIndex firstCell) := by
    change _∈gridPolylineSegments (translatePolyline _ _)
    rw [gridPolylineSegments_translatePolyline]
    exact List.mem_map.mpr ⟨first,firstMember,rfl⟩
  have secondLifted : second.translate (drawing.periodTranslation secondCell)∈
      gridPolylineSegments (drawing.realEdgeRoute secondIndex secondCell) := by
    change _∈gridPolylineSegments (translatePolyline _ _)
    rw [gridPolylineSegments_translatePolyline]
    exact List.mem_map.mpr ⟨second,secondMember,rfl⟩
  exact ⟨simple_segment_endpoint_of_mem firstSimple firstLifted endpoints.1 firstContains,
    simple_segment_endpoint_of_mem secondSimple secondLifted endpoints.2 secondContains⟩

theorem lifted_endpoint_agreement {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    {firstIndex secondIndex : Nat} (firstValid : firstIndex<drawing.edgeRoutes.length)
    (secondValid : secondIndex<drawing.edgeRoutes.length) (firstCell secondCell : Cell)
    (different : (firstIndex,firstCell)≠(secondIndex,secondCell))
    {first second : GridSegment} (firstMember : first∈gridPolylineSegments (drawing.edgeRoute firstIndex))
    (secondMember : second∈gridPolylineSegments (drawing.edgeRoute secondIndex)) (factor : Nat) (a b : Bool)
    (same : ((first.translate (drawing.periodTranslation firstCell)).oriented a).start=
      ((second.translate (drawing.periodTranslation secondCell)).oriented b).start) :
    ((first.mapPoints (liftedPoint drawing factor firstCell)).oriented a).start=
      ((second.mapPoints (liftedPoint drawing factor secondCell)).oriented b).start := by
  let q := ((first.translate (drawing.periodTranslation firstCell)).oriented a).start
  have firstContains : (first.translate (drawing.periodTranslation firstCell)).RealContains (realCell q) :=
    (GridSegment.oriented_contains _ _ _).mp (GridSegment.realContains_start _)
  have secondContains : (second.translate (drawing.periodTranslation secondCell)).RealContains (realCell q) := by
    rw [show q=((second.translate (drawing.periodTranslation secondCell)).oriented b).start from same]
    exact (GridSegment.oriented_contains _ _ _).mp (GridSegment.realContains_start _)
  have endpoints := planar.2 firstIndex secondIndex firstCell secondCell firstValid secondValid different (realCell q)
    (lifted_segment_in_route firstMember firstContains) (lifted_segment_in_route secondMember secondContains)
  have graphValid : firstIndex<source.edges.length := by rwa [planar.1.1.2.2.1] at firstValid
  let tagged : PeriodicEdge V × Nat := (source.edges[firstIndex],firstIndex)
  have taggedMember : tagged∈source.edges.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?,List.getElem?_eq_some_iff]
    exact ⟨graphValid,rfl⟩
  obtain ⟨vertex,vertexMember,cell,atVertex⟩ := real_endpoint_is_lifted_vertex planar.1.1 taggedMember firstCell endpoints.1
  have equal : q=Cell.add vertex (drawing.periodTranslation cell) := realCell_injective atVertex
  have bounds := planar.1.1.2.2.2.2.1 vertex vertexMember
  have firstEqual : Cell.add (drawing.periodTranslation firstCell) (first.oriented a).start=
      Cell.add vertex (drawing.periodTranslation cell) := by
    simpa only [q,translated_oriented_start] using equal
  have secondEqual : Cell.add (drawing.periodTranslation secondCell) (second.oriented b).start=
      Cell.add vertex (drawing.periodTranslation cell) := by
    simpa only [translated_oriented_start] using same.symm.trans equal
  rw [GridSegment.mapPoints_oriented_start,GridSegment.mapPoints_oriented_start]
  exact (liftedPoint_at_vertex bounds firstCell cell firstEqual).trans
    (liftedPoint_at_vertex bounds secondCell cell secondEqual).symm

end LeanTrominoes.PeriodicGridDrawing.InteriorBends
