/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridPolylineRealPointUniqueness
import LeanTrominoes.Common.Geometry.GridPolylineRealSegmentContacts

/-! # A listed point cannot occur in the interior of another simple-route piece -/
namespace LeanTrominoes.GridPolyline

theorem IsRealSimple.listed_point_segment_contact {route : List Cell} (simple : IsRealSimple route)
    {index : Nat} (valid : index+1 < route.length) {tagged : GridSegment × Nat}
    (member : tagged ∈ (gridPolylineSegments route).zipIdx)
    (contains : tagged.1.RealContains (realCell route[index])) :
    realCell route[index]=realCell tagged.1.start ∨ realCell route[index]=realCell tagged.1.finish := by
  obtain ⟨first,firstMember,firstStart,_⟩ := indexed_segment_at_point valid
  by_cases same : index=tagged.2
  · have firstLookup := List.mem_zipIdx_iff_getElem?.mp firstMember
    have taggedLookup := List.mem_zipIdx_iff_getElem?.mp member
    rw [same,taggedLookup] at firstLookup
    have equal := Option.some.inj firstLookup
    exact Or.inl (congrArg realCell (firstStart.symm.trans (congrArg GridSegment.start equal.symm)))
  · have contacts := simple.segment_contacts firstMember member same
    have firstContains : first.RealContains (realCell route[index]) := by rw [← firstStart]; exact GridSegment.realContains_start first
    exact (contacts _ firstContains contains).2

end LeanTrominoes.GridPolyline
