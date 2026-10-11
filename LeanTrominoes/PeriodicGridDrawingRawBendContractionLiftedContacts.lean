/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendContractionEndpointTransport

/-! # Distinct lifted original routes have endpoint-only contacts after joining -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement

theorem liftedRefinedPiece_occurrences_ne {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} {first second : (Nat × Nat) × PeriodicEdge (Vertex V)}
    (firstMember : first ∈ records source drawing)
    (secondMember : second ∈ records source drawing)
    (firstCopy secondCopy : Cell) (different : (first.1.1,firstCopy)≠(second.1.1,secondCopy)) :
    (recordIndex source drawing first,
      Cell.add (sourceCell drawing first.2.source) firstCopy)≠
    (recordIndex source drawing second,
      Cell.add (sourceCell drawing second.2.source) secondCopy) := by
  intro equal
  have indexEq : recordIndex source drawing first=
      recordIndex source drawing second := congrArg Prod.fst equal
  have firstAt := recordAt_recordIndex firstMember
  rw [indexEq,recordAt_recordIndex secondMember] at firstAt
  have recordEq : first=second := firstAt.symm
  subst second
  have copyEq := Cell.add_left_injective _ (congrArg Prod.snd equal)
  exact different (Prod.ext rfl copyEq)

theorem liftedContractedRoute_contacts {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    (degree : source.DegreeAtMost 4) {first second : PeriodicEdge V × Nat}
    (firstMember : first ∈ source.edges.zipIdx) (secondMember : second ∈ source.edges.zipIdx)
    (firstCopy secondCopy : Cell) (different : (first.2,firstCopy)≠(second.2,secondCopy)) {p : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains ((contractedRoute source drawing first).map
      (Cell.add (Cell.scale (cubicScale drawing*drawing.gridSize) firstCopy))) p)
    (secondContains : GridPolyline.RealContains ((contractedRoute source drawing second).map
      (Cell.add (Cell.scale (cubicScale drawing*drawing.gridSize) secondCopy))) p) :
    GridPolyline.RealIsEndpoint ((contractedRoute source drawing first).map
      (Cell.add (Cell.scale (cubicScale drawing*drawing.gridSize) firstCopy))) p ∧
    GridPolyline.RealIsEndpoint ((contractedRoute source drawing second).map
      (Cell.add (Cell.scale (cubicScale drawing*drawing.gridSize) secondCopy))) p := by
  obtain ⟨firstRecord,firstRecordMember,firstPieceContains⟩ :=
    liftedContractedRoute_contains planar degree firstMember firstCopy firstContains
  obtain ⟨secondRecord,secondRecordMember,secondPieceContains⟩ :=
    liftedContractedRoute_contains planar degree secondMember secondCopy secondContains
  have firstGlobal := parentRecord_mem firstMember firstRecordMember
  have secondGlobal := parentRecord_mem secondMember secondRecordMember
  have recordDifferent : (firstRecord.1.1,firstCopy)≠(secondRecord.1.1,secondCopy) := by
    simpa only [parentRecord_parent firstRecordMember,parentRecord_parent secondRecordMember] using different
  rw [liftedRefinedPiece_eq] at firstPieceContains secondPieceContains
  have rawContacts := distinct_lifted_pieceRoutes_contact planar degree localGraph localDrawing
    (recordIndex_tagged firstGlobal) (recordIndex_tagged secondGlobal)
    (Cell.add (sourceCell drawing firstRecord.2.source) firstCopy)
    (Cell.add (sourceCell drawing secondRecord.2.source) secondCopy)
    (liftedRefinedPiece_occurrences_ne firstGlobal secondGlobal firstCopy secondCopy recordDifferent)
    firstPieceContains secondPieceContains
  rw [record_lifted_segment_eq,record_lifted_segment_eq] at rawContacts
  have firstEnds := liftedRefinedPiece_endpoints source drawing firstRecord firstCopy
  have secondEnds := liftedRefinedPiece_endpoints source drawing secondRecord secondCopy
  have endpoints : GridPolyline.RealIsEndpoint (liftedRefinedPiece source drawing firstRecord firstCopy) p ∧
      GridPolyline.RealIsEndpoint (liftedRefinedPiece source drawing secondRecord secondCopy) p := by
    rw [GridPolyline.realIsEndpoint_iff_prescribed_endpoints firstEnds.1 firstEnds.2,
      GridPolyline.realIsEndpoint_iff_prescribed_endpoints secondEnds.1 secondEnds.2]
    exact rawContacts
  obtain ⟨a,firstOldContains,pointEq⟩ := liftedRefinedPiece_endpoint_preimage planar
    firstGlobal firstCopy endpoints.1
  obtain ⟨b,secondOldContains,secondPointEq⟩ := liftedRefinedPiece_endpoint_preimage planar
    secondGlobal secondCopy endpoints.2
  have scalePositive : (0:Int) < cubicScale drawing := by
    unfold cubicScale
    exact_mod_cast Nat.mul_pos (Cubic.rasterFactor_positive _) (Cubic.coreFactor_positive _)
  have equal : a=b := Cell.scale_injective scalePositive.ne' (realCell_injective (pointEq.symm.trans secondPointEq))
  subst b
  have oldEndpoints := planar.2 _ _ firstCopy secondCopy
    (record_parent_index_valid planar.1.1 firstGlobal) (record_parent_index_valid planar.1.1 secondGlobal)
    recordDifferent _ firstOldContains secondOldContains
  rw [parentRecord_parent firstRecordMember,parentRecord_parent secondRecordMember] at oldEndpoints
  rw [pointEq]
  exact ⟨liftedContractedRoute_endpoint_transport planar degree firstMember firstCopy oldEndpoints.1,
    liftedContractedRoute_endpoint_transport planar degree secondMember secondCopy oldEndpoints.2⟩

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
