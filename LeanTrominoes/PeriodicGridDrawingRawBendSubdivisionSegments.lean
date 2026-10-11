/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendSubdivisionCompatibility
import LeanTrominoes.PeriodicGridDrawingBendSubdivisionGlobalPoints
import LeanTrominoes.PeriodicGraphChainGeometry

/-! # Raw subdivision segments reproduce the original polygonal geometry -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision

def globalPoint {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) (entry : Vertex V × Cell) : Cell :=
  Cell.add (position source drawing entry.1) (Cell.scale drawing.gridSize entry.2)

theorem middle_globalPoints {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) (tagged : PeriodicEdge V × Nat) :
    (middle drawing tagged).map (globalPoint source drawing) = (drawing.edgeRoute tagged.2).tail.dropLast := by
  rw [middle,List.map_map]
  have mapped : (BendSubdivision.internalPoints drawing tagged.2).map
      (fun entry => globalPoint source drawing (Vertex.bend tagged.2 entry.2,cell drawing.gridSize entry.1)) =
      (BendSubdivision.internalPoints drawing tagged.2).map Prod.fst := by
    apply List.map_congr_left
    intro entry member
    simp only [globalPoint,position_middle source drawing tagged member]
    exact representative_lift _ _
  change (BendSubdivision.internalPoints drawing tagged.2).map
    (fun entry => globalPoint source drawing (Vertex.bend tagged.2 entry.2,cell drawing.gridSize entry.1)) = _
  rw [mapped,BendSubdivision.internalPoints_fst]

theorem nodes_globalPoints {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (valid : drawing.IsRealDrawing source)
    {tagged : PeriodicEdge V × Nat} (member : tagged ∈ source.edges.zipIdx) :
    (nodes tagged (middle drawing tagged)).map (globalPoint source drawing) = drawing.edgeRoute tagged.2 := by
  have endpoints := valid.1.2.2.2.2.2 tagged member
  have routeMember := edgeRoute_mem_of_compatible valid.1 member
  have reconstructed := BendSubdivision.route_eq_endpoints_and_internal (valid.2.1 _ routeMember).1 endpoints.1 endpoints.2
  rw [nodes,List.map_append,List.map_cons,List.map_cons,List.map_nil,middle_globalPoints]
  simpa only [globalPoint,position,Cell.add,Cell.scale,mul_zero,add_zero,List.cons_append,periodTranslation] using reconstructed.symm

def sourceCell {V : Type*} (drawing : PeriodicGridDrawing) : Vertex V → Cell
  | .original _ => (0,0)
  | .bend edgeIndex pointIndex => cell drawing.gridSize ((drawing.edgeRoute edgeIndex).getD pointIndex (0,0))

theorem nodes_source_labels {V : Type*} (drawing : PeriodicGridDrawing) (parent : PeriodicEdge V × Nat)
    {entry : Vertex V × Cell} (member : entry ∈ (nodes parent (middle drawing parent)).dropLast) :
    sourceCell drawing entry.1 = entry.2 := by
  rw [nodes,List.dropLast_concat,List.mem_cons] at member
  rcases member with rfl | member
  · rfl
  · obtain ⟨point,pointMember,rfl⟩ := List.mem_map.mp member
    simp only [sourceCell,(BendSubdivision.internalPoint_lookup pointMember).2.2]

theorem subdivision_absolute_segments {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (valid : drawing.IsRealDrawing source)
    {parent : PeriodicEdge V × Nat} (member : parent ∈ source.edges.zipIdx) :
    gridPolylineSegments (drawing.edgeRoute parent.2) =
      (chainEdges (nodes parent (middle drawing parent))).map
        (absoluteSegment (position source drawing) drawing.gridSize (sourceCell drawing)) := by
  rw [← nodes_globalPoints valid member]
  exact chainEdges_absoluteSegments _ _ _ (fun _ member => nodes_source_labels drawing parent member)

theorem indexed_absolute_segment {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (valid : drawing.IsRealDrawing source)
    {parent : PeriodicEdge V × Nat} (parentMember : parent ∈ source.edges.zipIdx)
    {piece : PeriodicEdge (Vertex V) × Nat} (pieceMember : piece ∈ (chainEdges (nodes parent (middle drawing parent))).zipIdx) :
    (absoluteSegment (position source drawing) drawing.gridSize (sourceCell drawing) piece.1,piece.2) ∈
      (gridPolylineSegments (drawing.edgeRoute parent.2)).zipIdx := by
  rw [subdivision_absolute_segments valid parentMember,List.zipIdx_map]
  exact List.mem_map.mpr ⟨piece,pieceMember,rfl⟩

theorem straightRoute_absolute_segment {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) (edge : PeriodicEdge (Vertex V)) :
    (GridSegment.mk (position source drawing edge.source)
      (Cell.add (position source drawing edge.target) (Cell.scale drawing.gridSize edge.offset))).translate
      (Cell.scale drawing.gridSize (sourceCell drawing edge.source)) =
    absoluteSegment (position source drawing) drawing.gridSize (sourceCell drawing) edge := by
  unfold GridSegment.translate absoluteSegment
  congr 1 <;> apply Prod.ext <;> simp only [Cell.add,Cell.scale] <;> ring

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
