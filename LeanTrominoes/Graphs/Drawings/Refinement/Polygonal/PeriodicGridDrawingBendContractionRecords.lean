/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingPolygonalSubdivisionRefinement

/-! # Recovering each orthogonal subedge by its original polygonal occurrence -/
namespace LeanTrominoes.PeriodicGridDrawing.BendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement PeriodicOrthocrossing

def recordIndex {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) (factor : Nat) (record : (Nat × Nat) × PeriodicEdge (Vertex V)) : Nat :=
  (records source drawing factor).idxOf record

theorem recordIndex_valid {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} {factor : Nat} {record : (Nat × Nat) × PeriodicEdge (Vertex V)}
    (member : record ∈ records source drawing factor) :
    recordIndex source drawing factor record < (subdivisionGraph source drawing factor).edges.length := by
  rw [← records_length]
  exact List.idxOf_lt_length_iff.mpr member

theorem recordAt_recordIndex {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} {factor : Nat} {record : (Nat × Nat) × PeriodicEdge (Vertex V)}
    (member : record ∈ records source drawing factor) :
    recordAt source drawing factor (recordIndex source drawing factor record)=record := by
  rw [recordAt,List.getD_eq_getElem?_getD]
  simp only [recordIndex,List.getElem?_idxOf member,Option.getD_some]

theorem recordIndex_tagged {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} {factor : Nat} {record : (Nat × Nat) × PeriodicEdge (Vertex V)}
    (member : record ∈ records source drawing factor) :
    (record.2,recordIndex source drawing factor record) ∈ (subdivisionGraph source drawing factor).edges.zipIdx := by
  rw [List.mem_zipIdx_iff_getElem?,← records_edges,List.getElem?_map]
  simp only [recordIndex,List.getElem?_idxOf member,Option.map_some]

def subdivisionScale (drawing : PeriodicGridDrawing) : Nat :=
  paddedRefinementFactor (bendRefinementFactor drawing*drawing.gridSize)

def refinedPiece {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) (record : (Nat × Nat) × PeriodicEdge (Vertex V)) : List Cell :=
  (orthogonalSubdivision source drawing).realEdgeRoute
    (recordIndex source drawing (bendRefinementFactor drawing) record)
    (sourceCell drawing (bendRefinementFactor drawing) record.2.source)

theorem orthogonalSubdivision_gridSize {V : Type*} [DecidableEq V]
    (source : PeriodicGraph V) (drawing : PeriodicGridDrawing) :
    (orthogonalSubdivision source drawing).gridSize=
      subdivisionScale drawing*(bendRefinementFactor drawing*drawing.gridSize) := by
  have positive : 0 < bendRefinementFactor drawing := by unfold bendRefinementFactor; omega
  rw [orthogonalSubdivision,straightRefinementDrawing_gridSize,
    subdivisionDrawing_gridSize source drawing positive]
  rfl

theorem refinedPiece_openSimple {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    (degree : source.DegreeAtMost 4) {record : (Nat × Nat) × PeriodicEdge (Vertex V)}
    (member : record ∈ records source drawing (bendRefinementFactor drawing)) :
    GridPolyline.IsRealOpenSimple (refinedPiece source drawing record) := by
  have spacing := bendRefinementFactor_spacing drawing
  have subPlanar := subdivisionDrawing_planar planar localDrawing localGraph spacing
  have subLocal := subdivisionGraph_local planar localDrawing localGraph (by omega : 2 < (bendRefinementFactor drawing:Int))
  have valid := straightRefinementRoute_valid subPlanar
    (subdivisionGraph_degreeAtMost degree (by omega) drawing _) subLocal
    (fun _ member => subdivisionDrawing_straight source drawing _ member) (recordIndex_tagged member)
  unfold refinedPiece realEdgeRoute orthogonalSubdivision
  rw [straightRefinementDrawing_edgeRoute (recordIndex_tagged member)]
  exact valid.1.translate _

end LeanTrominoes.PeriodicGridDrawing.BendSubdivision
