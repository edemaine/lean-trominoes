/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingBendContractionEndpointTransport

/-! # Distinct lifted original routes have endpoint-only contacts after joining -/
namespace LeanTrominoes.PeriodicGridDrawing.BendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement

private theorem refined_index_valid {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} {record : (Nat × Nat) × PeriodicEdge (Vertex V)}
    (member : record ∈ records source drawing (bendRefinementFactor drawing)) :
    recordIndex source drawing (bendRefinementFactor drawing) record < (orthogonalSubdivision source drawing).edgeRoutes.length := by
  simpa only [orthogonalSubdivision,straightRefinementDrawing,List.length_map,List.length_zipIdx] using recordIndex_valid member

theorem liftedRefinedPiece_occurrences_ne {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} {first second : (Nat × Nat) × PeriodicEdge (Vertex V)}
    (firstMember : first ∈ records source drawing (bendRefinementFactor drawing))
    (secondMember : second ∈ records source drawing (bendRefinementFactor drawing))
    (firstCopy secondCopy : Cell) (different : (first.1.1,firstCopy)≠(second.1.1,secondCopy)) :
    (recordIndex source drawing (bendRefinementFactor drawing) first,
      Cell.add (sourceCell drawing (bendRefinementFactor drawing) first.2.source) firstCopy)≠
    (recordIndex source drawing (bendRefinementFactor drawing) second,
      Cell.add (sourceCell drawing (bendRefinementFactor drawing) second.2.source) secondCopy) := by
  intro equal
  have indexEq : recordIndex source drawing (bendRefinementFactor drawing) first=
      recordIndex source drawing (bendRefinementFactor drawing) second := congrArg Prod.fst equal
  have firstAt := recordAt_recordIndex firstMember
  rw [indexEq,recordAt_recordIndex secondMember] at firstAt
  have recordEq : first=second := firstAt.symm
  subst second
  have copies := congrArg Prod.snd equal
  have x := congrArg Prod.fst copies
  have y := congrArg Prod.snd copies
  have copyEq : firstCopy=secondCopy := by
    exact Prod.ext (by simp only [Cell.add] at x; omega) (by simp only [Cell.add] at y; omega)
  exact different (Prod.ext rfl copyEq)

theorem liftedContractedRoute_contacts {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    (degree : source.DegreeAtMost 4) {first second : PeriodicEdge V × Nat}
    (firstMember : first ∈ source.edges.zipIdx) (secondMember : second ∈ source.edges.zipIdx)
    (firstCopy secondCopy : Cell) (different : (first.2,firstCopy)≠(second.2,secondCopy)) {p : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains ((contractedRoute source drawing first).map
      (Cell.add ((orthogonalSubdivision source drawing).periodTranslation firstCopy))) p)
    (secondContains : GridPolyline.RealContains ((contractedRoute source drawing second).map
      (Cell.add ((orthogonalSubdivision source drawing).periodTranslation secondCopy))) p) :
    GridPolyline.RealIsEndpoint ((contractedRoute source drawing first).map
      (Cell.add ((orthogonalSubdivision source drawing).periodTranslation firstCopy))) p ∧
    GridPolyline.RealIsEndpoint ((contractedRoute source drawing second).map
      (Cell.add ((orthogonalSubdivision source drawing).periodTranslation secondCopy))) p := by
  obtain ⟨firstRecord,firstRecordMember,firstPieceContains⟩ :=
    liftedContractedRoute_contains planar localDrawing localGraph degree firstMember firstCopy firstContains
  obtain ⟨secondRecord,secondRecordMember,secondPieceContains⟩ :=
    liftedContractedRoute_contains planar localDrawing localGraph degree secondMember secondCopy secondContains
  have firstGlobal := parentRecord_mem firstMember firstRecordMember
  have secondGlobal := parentRecord_mem secondMember secondRecordMember
  have outputPlanar := orthogonalSubdivision_planar planar localDrawing localGraph degree
  have recordDifferent : (firstRecord.1.1,firstCopy)≠(secondRecord.1.1,secondCopy) := by
    simpa only [parentRecord_parent firstRecordMember,parentRecord_parent secondRecordMember] using different
  rw [liftedRefinedPiece_eq] at firstPieceContains secondPieceContains
  have endpoints := outputPlanar.2 _ _ _ _ (refined_index_valid firstGlobal) (refined_index_valid secondGlobal)
    (liftedRefinedPiece_occurrences_ne firstGlobal secondGlobal firstCopy secondCopy recordDifferent) p
    firstPieceContains secondPieceContains
  rw [← liftedRefinedPiece_eq source drawing firstRecord firstCopy,
    ← liftedRefinedPiece_eq source drawing secondRecord secondCopy] at endpoints
  obtain ⟨a,firstOldContains,pointEq⟩ := liftedRefinedPiece_endpoint_preimage planar localDrawing localGraph degree
    firstGlobal firstCopy endpoints.1
  obtain ⟨b,secondOldContains,secondPointEq⟩ := liftedRefinedPiece_endpoint_preimage planar localDrawing localGraph degree
    secondGlobal secondCopy endpoints.2
  have scalePositive : (0:Int) < subdivisionScale drawing := by
    exact_mod_cast paddedRefinementFactor_positive (bendRefinementFactor drawing*drawing.gridSize)
  have equal : a=b := Cell.scale_injective scalePositive.ne' (realCell_injective (pointEq.symm.trans secondPointEq))
  subst b
  have movedPlanar := InteriorBends.perturbDrawing_planar planar localDrawing localGraph (bendRefinementFactor_spacing drawing)
  have oldEndpoints := movedPlanar.2 _ _ firstCopy secondCopy
    (record_parent_index_valid planar.1.1 firstGlobal) (record_parent_index_valid planar.1.1 secondGlobal)
    recordDifferent _ firstOldContains secondOldContains
  rw [parentRecord_parent firstRecordMember,parentRecord_parent secondRecordMember] at oldEndpoints
  rw [pointEq]
  exact ⟨liftedContractedRoute_endpoint_transport planar localDrawing localGraph degree firstMember firstCopy oldEndpoints.1,
    liftedContractedRoute_endpoint_transport planar localDrawing localGraph degree secondMember secondCopy oldEndpoints.2⟩

end LeanTrominoes.PeriodicGridDrawing.BendSubdivision
