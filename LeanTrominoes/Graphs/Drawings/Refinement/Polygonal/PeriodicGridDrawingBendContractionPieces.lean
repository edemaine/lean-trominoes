/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingBendContractionPieceEndpoints
import LeanTrominoes.Common.Geometry.GridPolylineRealRouteChain

/-! # Ordered orthogonal pieces of each original polygonal protoedge -/
namespace LeanTrominoes.PeriodicGridDrawing.BendSubdivision
open PeriodicGraph.BendSubdivision

def parentRecords {V : Type*} (drawing : PeriodicGridDrawing) (factor : Nat) (parent : PeriodicEdge V × Nat) :
    List ((Nat × Nat) × PeriodicEdge (Vertex V)) :=
  (chainEdges (nodes parent (middle drawing factor parent))).zipIdx.map fun piece => ((parent.2,piece.2),piece.1)

def parentPieces {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (parent : PeriodicEdge V × Nat) : List (List Cell) :=
  (parentRecords drawing (bendRefinementFactor drawing) parent).map (refinedPiece source drawing)

def contractedRoute {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (parent : PeriodicEdge V × Nat) : List Cell :=
  GridPolyline.joinRouteChain (parentPieces source drawing parent)

theorem parentRecord_mem {V : Type*} {source : PeriodicGraph V} {drawing : PeriodicGridDrawing} {factor : Nat}
    {parent : PeriodicEdge V × Nat} (parentMember : parent ∈ source.edges.zipIdx)
    {record : (Nat × Nat) × PeriodicEdge (Vertex V)} (member : record ∈ parentRecords drawing factor parent) :
    record ∈ records source drawing factor := List.mem_flatMap.mpr ⟨parent,parentMember,member⟩

theorem parentRecord_key {V : Type*} (drawing : PeriodicGridDrawing) (factor : Nat)
    (parent : PeriodicEdge V × Nat) {index : Nat} (valid : index < (parentRecords drawing factor parent).length) :
    (parentRecords drawing factor parent)[index].1=(parent.2,index) := by
  simp only [parentRecords,List.getElem_map,List.getElem_zipIdx,Nat.zero_add]

theorem parentRecords_length {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source) (factor : Nat)
    {parent : PeriodicEdge V × Nat} (member : parent ∈ source.edges.zipIdx) :
    (parentRecords drawing factor parent).length=
      (gridPolylineSegments ((InteriorBends.perturbDrawing drawing factor).edgeRoute parent.2)).length := by
  rw [InteriorBends.perturbDrawing_edgeRoute,subdivision_absolute_segments planar factor member]
  simp only [parentRecords,List.length_map,List.length_zipIdx]

theorem parentPieces_length {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    {parent : PeriodicEdge V × Nat} (member : parent ∈ source.edges.zipIdx) :
    (parentPieces source drawing parent).length=
      (gridPolylineSegments ((InteriorBends.perturbDrawing drawing (bendRefinementFactor drawing)).edgeRoute parent.2)).length := by
  exact (List.length_map _).trans (parentRecords_length planar _ member)

theorem parentPiece_data {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    {parent : PeriodicEdge V × Nat} (parentMember : parent ∈ source.edges.zipIdx)
    {index : Nat} (valid : index < (parentPieces source drawing parent).length) :
    ∃ record ∈ records source drawing (bendRefinementFactor drawing),
      record.1=(parent.2,index) ∧ (parentPieces source drawing parent)[index]=refinedPiece source drawing record ∧
      (absoluteSegment (position source drawing (bendRefinementFactor drawing))
        ((bendRefinementFactor drawing:Int)*drawing.gridSize) (sourceCell drawing (bendRefinementFactor drawing)) record.2,index) ∈
      (gridPolylineSegments ((InteriorBends.perturbDrawing drawing (bendRefinementFactor drawing)).edgeRoute parent.2)).zipIdx := by
  have recordValid : index < (parentRecords drawing (bendRefinementFactor drawing) parent).length := by
    simpa only [parentPieces,List.length_map] using valid
  let record := (parentRecords drawing (bendRefinementFactor drawing) parent)[index]'recordValid
  have member := parentRecord_mem parentMember (List.getElem_mem recordValid)
  have key := parentRecord_key drawing (bendRefinementFactor drawing) parent recordValid
  have pieceMember := record_segment_in_moved_route planar member
  rw [key] at pieceMember
  exact ⟨record,member,key,by simp only [parentPieces,List.getElem_map]; rfl,pieceMember⟩

end LeanTrominoes.PeriodicGridDrawing.BendSubdivision
