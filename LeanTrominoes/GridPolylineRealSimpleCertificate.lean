/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentRealBoxIntersection
import LeanTrominoes.PeriodicGridDrawingRealGeometry

/-! # Finite closed-box certificates for simple open grid routes -/
namespace LeanTrominoes.GridPolyline

def SimpleBoxCertificate (route : List Cell) : Prop :=
  2 ≤ route.length ∧
    (∀ segment ∈ gridPolylineSegments route, segment.start ≠ segment.finish) ∧
    ∀ first ∈ (gridPolylineSegments route).zipIdx,
      ∀ second ∈ (gridPolylineSegments route).zipIdx, first.2 < second.2 →
        (max (min first.1.start.1 first.1.finish.1) (min second.1.start.1 second.1.finish.1) ≤
            min (max first.1.start.1 first.1.finish.1) (max second.1.start.1 second.1.finish.1) ∧
          max (min first.1.start.2 first.1.finish.2) (min second.1.start.2 second.1.finish.2) ≤
            min (max first.1.start.2 first.1.finish.2) (max second.1.start.2 second.1.finish.2)) →
        first.2+1 = second.2 ∧ GridSegment.BoxIntersectionIsPoint first.1 second.1 first.1.finish

instance (route : List Cell) : Decidable (SimpleBoxCertificate route) := by
  unfold SimpleBoxCertificate
  infer_instance

theorem isRealSimple_of_box_certificate {route : List Cell} (certificate : SimpleBoxCertificate route) :
    IsRealSimple route := by
  refine ⟨certificate.1,certificate.2.1,?_⟩
  intro first firstMember second secondMember ordered point firstContains secondContains
  have firstBox := GridSegment.realBoxContains_of_realContains firstContains
  have secondBox := GridSegment.realBoxContains_of_realContains secondContains
  have occupied :
      max (min first.1.start.1 first.1.finish.1) (min second.1.start.1 second.1.finish.1) ≤
          min (max first.1.start.1 first.1.finish.1) (max second.1.start.1 second.1.finish.1) ∧
        max (min first.1.start.2 first.1.finish.2) (min second.1.start.2 second.1.finish.2) ≤
          min (max first.1.start.2 first.1.finish.2) (max second.1.start.2 second.1.finish.2) := by
    constructor
    · apply max_le <;> apply le_min
      · exact_mod_cast le_trans firstBox.1 firstBox.2.1
      · exact_mod_cast le_trans firstBox.1 secondBox.2.1
      · exact_mod_cast le_trans secondBox.1 firstBox.2.1
      · exact_mod_cast le_trans secondBox.1 secondBox.2.1
    · apply max_le <;> apply le_min
      · exact_mod_cast le_trans firstBox.2.2.1 firstBox.2.2.2
      · exact_mod_cast le_trans firstBox.2.2.1 secondBox.2.2.2
      · exact_mod_cast le_trans secondBox.2.2.1 firstBox.2.2.2
      · exact_mod_cast le_trans secondBox.2.2.1 secondBox.2.2.2
  have verified := certificate.2.2 first firstMember second secondMember ordered occupied
  exact Or.inl ⟨verified.1,GridSegment.real_intersection_eq_of_box_certificate verified.2 firstContains secondContains⟩

end LeanTrominoes.GridPolyline
