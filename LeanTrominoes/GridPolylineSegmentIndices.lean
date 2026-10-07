/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawing
import Mathlib.Tactic

/-! # Endpoint indices of consecutive polyline segments -/
namespace LeanTrominoes

theorem gridPolylineSegments_getElem?_eq_some_iff (route : List Cell) (index : Nat) (segment : GridSegment) :
    (gridPolylineSegments route)[index]? = some segment ↔
      route[index]? = some segment.start ∧ route[index+1]? = some segment.finish := by
  induction route generalizing index with
  | nil => simp [gridPolylineSegments]
  | cons first rest ih =>
      cases rest with
      | nil => cases index <;> simp [gridPolylineSegments]
      | cons second tail =>
          cases index with
          | zero =>
              cases segment
              simp [gridPolylineSegments,GridSegment.mk.injEq]
          | succ index =>
              simpa [gridPolylineSegments,Nat.add_assoc] using ih index

theorem indexed_gridPolylineSegment_endpoints {route : List Cell} {tagged : GridSegment × Nat}
    (member : tagged ∈ (gridPolylineSegments route).zipIdx) :
    route[tagged.2]? = some tagged.1.start ∧ route[tagged.2+1]? = some tagged.1.finish := by
  exact (gridPolylineSegments_getElem?_eq_some_iff route tagged.2 tagged.1).mp
    (List.mem_zipIdx_iff_getElem?.mp member)

theorem indexed_gridPolylineSegments_consecutive {route : List Cell} {first second : GridSegment × Nat}
    (firstMember : first ∈ (gridPolylineSegments route).zipIdx)
    (secondMember : second ∈ (gridPolylineSegments route).zipIdx)
    (adjacent : first.2+1 = second.2) : first.1.finish = second.1.start := by
  have firstEnds := indexed_gridPolylineSegment_endpoints firstMember
  have secondEnds := indexed_gridPolylineSegment_endpoints secondMember
  rw [adjacent,secondEnds.1] at firstEnds
  exact Option.some.inj firstEnds.2.symm

end LeanTrominoes
