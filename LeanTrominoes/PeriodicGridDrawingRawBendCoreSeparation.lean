/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendLiftedVertexUniqueness

/-! # Global separation of all distinct digital-core occurrences

Disjoint original pieces use integer separating axes. Pieces meeting at a
vertex use the incidence order, for either endpoint and every periodic copy.
-/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem distinct_lifted_coreRoutes_disjoint {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    (graphLocal : source.IsLocal) (drawingLocal : drawing.IsRealLocal source)
    {first second : PeriodicEdge (Vertex V) × Nat}
    (firstMember : first ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (secondMember : second ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (firstCopy secondCopy : Cell) (different : (first.2,firstCopy) ≠ (second.2,secondCopy))
    {point : ℝ × ℝ} (firstContains : GridPolyline.RealContains (liftedCoreRoute source drawing first firstCopy) point) :
    ¬GridPolyline.RealContains (liftedCoreRoute source drawing second secondCopy) point := by
  classical
  by_cases disjoint : ∀ original : ℝ × ℝ,
      ((subdivisionSegment source drawing first.1).translate (drawing.periodTranslation firstCopy)).RealContains original →
      ¬((subdivisionSegment source drawing second.1).translate (drawing.periodTranslation secondCopy)).RealContains original
  · exact liftedCoreRoutes_disjoint planar graphLocal drawingLocal firstMember secondMember firstCopy secondCopy disjoint firstContains
  · push_neg at disjoint
    obtain ⟨original,firstOriginal,secondOriginal⟩ := disjoint
    obtain ⟨firstEndpoints,secondEndpoints⟩ := subdivision_segment_contacts planar firstMember secondMember firstCopy secondCopy different
      original firstOriginal secondOriginal
    obtain ⟨firstTarget,firstEndpoint⟩ : ∃ target : Bool,
        original = realCell (liftedIncidentRawSegment source drawing first target firstCopy).start := by
      rcases firstEndpoints with endpoint | endpoint
      · exact ⟨false,endpoint⟩
      · exact ⟨true,endpoint⟩
    obtain ⟨secondTarget,secondEndpoint⟩ : ∃ target : Bool,
        original = realCell (liftedIncidentRawSegment source drawing second target secondCopy).start := by
      rcases secondEndpoints with endpoint | endpoint
      · exact ⟨false,endpoint⟩
      · exact ⟨true,endpoint⟩
    have sameStart := realCell_injective (firstEndpoint.symm.trans secondEndpoint)
    have sameVertex := (lifted_incident_start_unique planar firstMember secondMember firstTarget secondTarget firstCopy secondCopy sameStart).1
    have portsDifferent := lifted_incident_ports_ne planar firstMember secondMember firstTarget secondTarget firstCopy secondCopy sameStart different
    exact lifted_incident_coreRoutes_disjoint planar degree graphLocal drawingLocal firstMember secondMember
      firstTarget secondTarget firstCopy secondCopy sameVertex sameStart portsDifferent firstContains

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
