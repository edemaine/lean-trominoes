/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendContractionRecords
import LeanTrominoes.GridPolylineRealRouteChain

/-! # Ordered orthogonal pieces of each original polygonal protoedge -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision

def parentRecords {V : Type*} (drawing : PeriodicGridDrawing) (parent : PeriodicEdge V × Nat) :
    List ((Nat × Nat) × PeriodicEdge (Vertex V)) :=
  (chainEdges (nodes parent (middle drawing parent))).zipIdx.map fun piece => ((parent.2,piece.2),piece.1)

noncomputable def parentPieces {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (parent : PeriodicEdge V × Nat) : List (List Cell) :=
  (parentRecords drawing parent).map (refinedPiece source drawing)

noncomputable def contractedRoute {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (parent : PeriodicEdge V × Nat) : List Cell :=
  GridPolyline.joinRouteChain (parentPieces source drawing parent)

theorem parentRecord_mem {V : Type*} {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    {parent : PeriodicEdge V × Nat} (parentMember : parent ∈ source.edges.zipIdx)
    {record : (Nat × Nat) × PeriodicEdge (Vertex V)} (member : record ∈ parentRecords drawing parent) :
    record ∈ records source drawing := List.mem_flatMap.mpr ⟨parent,parentMember,member⟩

theorem parentRecord_key {V : Type*} (drawing : PeriodicGridDrawing)
    (parent : PeriodicEdge V × Nat) {index : Nat} (valid : index < (parentRecords drawing parent).length) :
    (parentRecords drawing parent)[index].1=(parent.2,index) := by
  simp only [parentRecords,List.getElem_map,List.getElem_zipIdx,Nat.zero_add]

theorem parentRecords_length {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    {parent : PeriodicEdge V × Nat} (member : parent ∈ source.edges.zipIdx) :
    (parentRecords drawing parent).length=
      (gridPolylineSegments (drawing.edgeRoute parent.2)).length := by
  rw [subdivision_absolute_segments planar.1 member]
  simp only [parentRecords,List.length_map,List.length_zipIdx]

theorem parentPieces_length {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    {parent : PeriodicEdge V × Nat} (member : parent ∈ source.edges.zipIdx) :
    (parentPieces source drawing parent).length=
      (gridPolylineSegments (drawing.edgeRoute parent.2)).length := by
  exact (List.length_map _).trans (parentRecords_length planar member)

theorem parentPiece_data {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    {parent : PeriodicEdge V × Nat} (parentMember : parent ∈ source.edges.zipIdx)
    {index : Nat} (valid : index < (parentPieces source drawing parent).length) :
    ∃ record ∈ records source drawing,
      record.1=(parent.2,index) ∧ (parentPieces source drawing parent)[index]=refinedPiece source drawing record ∧
      (absoluteSegment (position source drawing)
        drawing.gridSize (sourceCell drawing) record.2,index) ∈
      (gridPolylineSegments (drawing.edgeRoute parent.2)).zipIdx := by
  have recordValid : index < (parentRecords drawing parent).length := by
    simpa only [parentPieces,List.length_map] using valid
  let record := (parentRecords drawing parent)[index]'recordValid
  have member := parentRecord_mem parentMember (List.getElem_mem recordValid)
  have key := parentRecord_key drawing parent recordValid
  have pieceMember := record_segment_in_original_route planar.1 member
  rw [key] at pieceMember
  exact ⟨record,member,key,by simp only [parentPieces,List.getElem_map]; rfl,pieceMember⟩

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
