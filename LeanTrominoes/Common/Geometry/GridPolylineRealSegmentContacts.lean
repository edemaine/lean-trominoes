/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentPerturbationContacts
import LeanTrominoes.Common.Geometry.GridPolylineRealSimpleEndpointIndices

/-! # Segment contacts inside a simple polygonal route -/
namespace LeanTrominoes.GridPolyline

theorem IsRealSimple.segment_contacts {route : List Cell} (simple : IsRealSimple route)
    {first second : GridSegment × Nat}
    (firstMember : first∈(gridPolylineSegments route).zipIdx)
    (secondMember : second∈(gridPolylineSegments route).zipIdx)
    (different : first.2≠second.2) : GridSegment.EndpointContacts first.1 second.1 := by
  have orderedContacts {a b : GridSegment × Nat}
      (am : a∈(gridPolylineSegments route).zipIdx) (bm : b∈(gridPolylineSegments route).zipIdx)
      (ordered : a.2<b.2) : GridSegment.EndpointContacts a.1 b.1 := by
    intro p ap bp
    rcases simple.2.2 a am b bm ordered p ap bp with adjacent | closed
    · have boundary := indexed_gridPolylineSegments_consecutive am bm adjacent.1
      exact ⟨Or.inr adjacent.2,Or.inl (by simpa only [boundary] using adjacent.2)⟩
    · exact ⟨Or.inl closed.2.2.1,Or.inr closed.2.2.2⟩
  rcases lt_or_gt_of_ne different with ordered | ordered
  · exact orderedContacts firstMember secondMember ordered
  · intro p ap bp
    have contacts := orderedContacts secondMember firstMember ordered p bp ap
    exact ⟨contacts.2,contacts.1⟩

theorem IsRealSimple.endpoint_segment_contact {route : List Cell} (simple : IsRealSimple route)
    {tagged : GridSegment × Nat} (member : tagged∈(gridPolylineSegments route).zipIdx)
    {p : ℝ × ℝ} (endpoint : RealIsEndpoint route p) (contains : tagged.1.RealContains p) :
    p=realCell tagged.1.start ∨ p=realCell tagged.1.finish := by
  obtain ⟨actual,equal⟩ : ∃ actual : Cell, p=realCell actual := by
    rcases endpoint with ⟨actual,_,equal⟩ | ⟨actual,_,equal⟩ <;> exact ⟨actual,equal⟩
  subst p
  rcases simple.endpoint_contact_piece endpoint member contains with atHead | atLast
  · exact Or.inl (by rw [atHead.2])
  · exact Or.inr (by rw [atLast.2])

end LeanTrominoes.GridPolyline
