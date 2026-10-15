/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingBendSubdivisionGlobalPoints
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingBendSubdivisionRecords
import LeanTrominoes.Graphs.Core.PeriodicGraphChainGeometry

/-! # Subdivision segments reproduce the moved polygonal segment occurrences -/
namespace LeanTrominoes.PeriodicGridDrawing.BendSubdivision
open PeriodicGraph.BendSubdivision

def sourceCell {V : Type*} (drawing : PeriodicGridDrawing) (factor : Nat) : Vertex V → Cell
  | .original _ => (0,0)
  | .bend edgeIndex pointIndex => InteriorBends.cell drawing.gridSize factor
      ((drawing.edgeRoute edgeIndex).getD pointIndex (0,0))

theorem nodes_source_labels {V : Type*} (drawing : PeriodicGridDrawing) (factor : Nat)
    (parent : PeriodicEdge V × Nat) {entry : Vertex V × Cell}
    (member : entry∈(nodes parent (middle drawing factor parent)).dropLast) :
    sourceCell drawing factor entry.1=entry.2 := by
  rw [nodes,List.dropLast_concat,List.mem_cons] at member
  rcases member with rfl | member
  · rfl
  · obtain ⟨point,pointMember,rfl⟩ := List.mem_map.mp member
    simp only [sourceCell,(internalPoint_lookup pointMember).2.2]

theorem subdivision_absolute_segments {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source) (factor : Nat)
    {parent : PeriodicEdge V × Nat} (member : parent∈source.edges.zipIdx) :
    gridPolylineSegments ((drawing.edgeRoute parent.2).map (InteriorBends.point drawing.gridSize factor))=
      (chainEdges (nodes parent (middle drawing factor parent))).map
        (absoluteSegment (position source drawing factor) ((factor:Int)*drawing.gridSize) (sourceCell drawing factor)) := by
  rw [← nodes_globalPoints planar factor member]
  exact chainEdges_absoluteSegments _ _ _ (fun _ member => nodes_source_labels drawing factor parent member)

theorem indexed_absolute_segment {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source) (factor : Nat)
    {parent : PeriodicEdge V × Nat} (parentMember : parent∈source.edges.zipIdx)
    {piece : PeriodicEdge (Vertex V) × Nat}
    (pieceMember : piece∈(chainEdges (nodes parent (middle drawing factor parent))).zipIdx) :
    (absoluteSegment (position source drawing factor) ((factor:Int)*drawing.gridSize)
      (sourceCell drawing factor) piece.1,piece.2)∈
      (gridPolylineSegments ((drawing.edgeRoute parent.2).map (InteriorBends.point drawing.gridSize factor))).zipIdx := by
  rw [subdivision_absolute_segments planar factor parentMember,List.zipIdx_map]
  exact List.mem_map.mpr ⟨piece,pieceMember,rfl⟩

theorem record_absolute_segment_member {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source) {factor : Nat}
    {record : (Nat × Nat) × PeriodicEdge (Vertex V)} (member : record∈records source drawing factor) :
    ∃ parent∈source.edges.zipIdx, parent.2=record.1.1 ∧
      (absoluteSegment (position source drawing factor) ((factor:Int)*drawing.gridSize)
        (sourceCell drawing factor) record.2,record.1.2)∈
        (gridPolylineSegments ((drawing.edgeRoute parent.2).map (InteriorBends.point drawing.gridSize factor))).zipIdx := by
  obtain ⟨parent,parentMember,piece,pieceMember,rfl⟩ := record_provenance member
  exact ⟨parent,parentMember,rfl,indexed_absolute_segment planar factor parentMember pieceMember⟩

theorem straightRoute_absolute_segment {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) (factor : Nat) (edge : PeriodicEdge (Vertex V)) :
    (GridSegment.mk (position source drawing factor edge.source)
      (Cell.add (position source drawing factor edge.target) (Cell.scale (factor*drawing.gridSize) edge.offset))).translate
      (Cell.scale ((factor:Int)*drawing.gridSize) (sourceCell drawing factor edge.source))=
    absoluteSegment (position source drawing factor) ((factor:Int)*drawing.gridSize) (sourceCell drawing factor) edge := by
  unfold GridSegment.translate absoluteSegment
  congr 1 <;> apply Prod.ext <;> simp only [Cell.add,Cell.scale] <;> ring

end LeanTrominoes.PeriodicGridDrawing.BendSubdivision
