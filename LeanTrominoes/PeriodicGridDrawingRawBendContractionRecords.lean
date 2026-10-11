/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendPieceContacts
import LeanTrominoes.PeriodicGridDrawingRawBendParentPieceFanLocality
import LeanTrominoes.GridPolylineRealReplacementContacts

/-! # Recovering cubic piece routes by their original polygonal occurrences -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement PeriodicOrthocrossing

def recordIndex {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) (record : (Nat × Nat) × PeriodicEdge (Vertex V)) : Nat :=
  (records source drawing).idxOf record

theorem recordIndex_valid {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} {record : (Nat × Nat) × PeriodicEdge (Vertex V)}
    (member : record ∈ records source drawing) :
    recordIndex source drawing record < (subdivisionGraph source drawing).edges.length := by
  rw [← records_length]
  exact List.idxOf_lt_length_iff.mpr member

theorem recordAt_recordIndex {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} {record : (Nat × Nat) × PeriodicEdge (Vertex V)}
    (member : record ∈ records source drawing) : recordAt source drawing (recordIndex source drawing record)=record := by
  rw [recordAt,List.getD_eq_getElem?_getD]
  simp only [recordIndex,List.getElem?_idxOf member,Option.getD_some]

theorem recordIndex_tagged {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} {record : (Nat × Nat) × PeriodicEdge (Vertex V)}
    (member : record ∈ records source drawing) :
    (record.2,recordIndex source drawing record) ∈ (subdivisionGraph source drawing).edges.zipIdx := by
  rw [List.mem_zipIdx_iff_getElem?,← records_edges,List.getElem?_map]
  simp only [recordIndex,List.getElem?_idxOf member,Option.map_some]

noncomputable def refinedPiece {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) (record : (Nat × Nat) × PeriodicEdge (Vertex V)) : List Cell :=
  liftedPieceRoute source drawing (record.2,recordIndex source drawing record) (sourceCell drawing record.2.source)

/-- The record's source-cell label restores its absolute parent-segment coordinates. -/
theorem record_lifted_segment_eq {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) (record : (Nat × Nat) × PeriodicEdge (Vertex V)) (copy : Cell) :
    (subdivisionSegment source drawing record.2).translate
        (drawing.periodTranslation (Cell.add (sourceCell drawing record.2.source) copy)) =
      (absoluteSegment (position source drawing) drawing.gridSize (sourceCell drawing) record.2).translate
        (drawing.periodTranslation copy) := by
  rw [lifted_subdivision_segment_eq]
  congr 2
  apply Prod.ext <;> simp only [Cell.add,Cell.sub] <;> ring

theorem refinedPiece_openSimple {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    {record : (Nat × Nat) × PeriodicEdge (Vertex V)} (member : record ∈ records source drawing) :
    GridPolyline.IsRealOpenSimple (refinedPiece source drawing record) :=
  liftedPieceRoute_simple planar degree (recordIndex_tagged member) _

theorem refinedPiece_endpoints {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) (record : (Nat × Nat) × PeriodicEdge (Vertex V)) :
    (refinedPiece source drawing record).head?=some (Cell.scale (cubicScale drawing)
      (absoluteSegment (position source drawing) drawing.gridSize (sourceCell drawing) record.2).start) ∧
    (refinedPiece source drawing record).getLast?=some (Cell.scale (cubicScale drawing)
      (absoluteSegment (position source drawing) drawing.gridSize (sourceCell drawing) record.2).finish) := by
  have endpoints := pieceRoute_endpoints source drawing (record.2,recordIndex source drawing record)
  simp only [refinedPiece,liftedPieceRoute,translatePolyline,List.head?_map,List.getLast?_map,
    endpoints.1,endpoints.2,Option.map_some]
  constructor <;> apply congrArg some <;> apply Prod.ext <;>
    simp only [absoluteSegment,subdivisionSegment,cubicScale,Cell.add,Cell.scale] <;> ring

theorem refinedPiece_endpoint_contacts {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal) (degree : source.DegreeAtMost 4)
    {first second : (Nat × Nat) × PeriodicEdge (Vertex V)}
    (firstMember : first ∈ records source drawing) (secondMember : second ∈ records source drawing)
    (different : first.1≠second.1) {p : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (refinedPiece source drawing first) p)
    (secondContains : GridPolyline.RealContains (refinedPiece source drawing second) p) :
    GridPolyline.RealIsEndpoint (refinedPiece source drawing first) p ∧
      GridPolyline.RealIsEndpoint (refinedPiece source drawing second) p := by
  have indicesDifferent : recordIndex source drawing first ≠ recordIndex source drawing second := by
    intro equal
    have recordsEqual := (recordAt_recordIndex firstMember).symm.trans (equal ▸ recordAt_recordIndex secondMember)
    exact different (congrArg Prod.fst recordsEqual)
  have contacts := distinct_lifted_pieceRoutes_contact planar degree localGraph localDrawing
    (recordIndex_tagged firstMember) (recordIndex_tagged secondMember)
    (sourceCell drawing first.2.source) (sourceCell drawing second.2.source)
    (fun equal => indicesDifferent (congrArg Prod.fst equal)) firstContains secondContains
  have absolute (edge : PeriodicEdge (Vertex V)) :
      (subdivisionSegment source drawing edge).translate (drawing.periodTranslation (sourceCell drawing edge.source)) =
        absoluteSegment (position source drawing) drawing.gridSize (sourceCell drawing) edge :=
    liftedIncidentRawSegment_absolute source drawing (edge,0) false
  rw [absolute,absolute] at contacts
  have firstEnds := refinedPiece_endpoints source drawing first
  have secondEnds := refinedPiece_endpoints source drawing second
  rw [GridPolyline.realIsEndpoint_iff_prescribed_endpoints firstEnds.1 firstEnds.2,
    GridPolyline.realIsEndpoint_iff_prescribed_endpoints secondEnds.1 secondEnds.2]
  exact contacts

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
