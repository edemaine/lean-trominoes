/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineUnitSubdivisionContacts
import LeanTrominoes.OrthogonalPolylineUnitSubdivisionJoin
import LeanTrominoes.RetainedAngularFanDirectSourceFirstDirections

/-! # Source-head isolation of the finite direct-source Figure 7 atlas -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

/-- Finite segment-level test that the first point is neither listed nor
contained in any segment after the route's first segment. -/
def routeHeadGeometricallyFresh (points : List Cell) : Bool :=
  match points.head? with
  | none => true
  | some head =>
      decide (head ∉ points.tail) &&
        (gridPolylineSegments points.tail).all fun segment =>
          decide (¬ segment.Contains head)

/-- The compact segment-level test implies source-head isolation after unit
subdivision, without constructing the subdivided route during finite atlas
verification. -/
theorem headNotInTail_unitSubdividePolyline_of_routeHeadGeometricallyFresh
    {points : List Cell}
    (orthogonal : PeriodicOrthocrossing.OrthogonalPolyline points)
    (checked : routeHeadGeometricallyFresh points = true) :
    AxisDirection.HeadNotInTail
      (AxisDirection.unitSubdividePolyline points) := by
  induction points using List.twoStepInduction with
  | nil => simp [AxisDirection.HeadNotInTail]
  | singleton point => simp [AxisDirection.HeadNotInTail]
  | cons_cons first second rest _induction =>
      have orthogonalParts :=
        (List.isChain_cons_cons.mp orthogonal :
          (GridSegment.mk first second).IsAxisAligned ∧
            PeriodicOrthocrossing.OrthogonalPolyline (second :: rest))
      have checkedParts :
          decide (first ∉ second :: rest) = true ∧
            (gridPolylineSegments (second :: rest)).all
                (fun segment => decide (¬ segment.Contains first)) = true := by
        simpa [routeHeadGeometricallyFresh] using
          checked
      have firstNotInTail : first ∉ second :: rest :=
        of_decide_eq_true checkedParts.1
      have firstNotInSubdividedTail :
          first ∉
            AxisDirection.unitSubdividePolyline (second :: rest) := by
        intro member
        rcases
            AxisDirection.unitSubdividePolyline_mem_original_or_segmentInterior
              orthogonalParts.2 member with
          originalMember | ⟨segment, segmentMember, interior⟩
        · exact firstNotInTail originalMember
        · have segmentChecked :=
            (List.all_eq_true.mp checkedParts.2)
              segment segmentMember
          exact (of_decide_eq_true segmentChecked)
            (GridSegment.contains_of_interiorContains interior)
      have firstSegmentFresh :
          AxisDirection.HeadNotInTail
            (AxisDirection.unitSegmentPoints first second) :=
        AxisDirection.headNotInTail_of_nodup
          (AxisDirection.unitSegmentPoints_nodup orthogonalParts.1)
      rw [AxisDirection.unitSubdividePolyline]
      apply firstSegmentFresh.joinAtEndpoint
      · exact AxisDirection.unitSegmentPoints_head? first second
      · intro member
        exact firstNotInSubdividedTail (List.mem_of_mem_tail member)

/-- Every origin-zero direct-source Figure 7 route passes the compact
segment-level source-head isolation test. -/
theorem retainedDirectSourceZeroCompleteFigure7Route_headFresh_checked :
    ∀ (kind : RetainedDirectClauseKind)
      (index : Fin (retainedDirectSourcePrefixChoices kind).length)
      (slot : RetainedTerminalSlot),
      routeHeadGeometricallyFresh
          ((retainedDirectSourceZeroChoice kind index).completeFigure7Route
            slot) = true := by
  native_decide

/-- Every origin-zero direct-source Figure 7 route retains an isolated
source endpoint after unit subdivision. -/
theorem retainedDirectSourceZeroCompleteFigure7Route_headNotInTail
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (slot : RetainedTerminalSlot) :
    AxisDirection.HeadNotInTail
      (AxisDirection.unitSubdividePolyline
        ((retainedDirectSourceZeroChoice kind index).completeFigure7Route
          slot)) := by
  exact
    headNotInTail_unitSubdividePolyline_of_routeHeadGeometricallyFresh
      (retainedDirectSourceZeroCompleteFigure7Route_valid
        kind index slot).2
      (retainedDirectSourceZeroCompleteFigure7Route_headFresh_checked
        kind index slot)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
