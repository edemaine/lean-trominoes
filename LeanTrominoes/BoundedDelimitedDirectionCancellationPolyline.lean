/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoundedDelimitedDirectionCancellationPrefix
import LeanTrominoes.GadgetSparseRouteDirectionNormalization
import LeanTrominoes.OrthogonalPolylineEndpointDirectionSeparation
import LeanTrominoes.OrthogonalPolylineUnitSubdivisionSimplicity

/-! # Nonreversal facts for unit-subdivision direction words -/

namespace LeanTrominoes
namespace BoundedDelimitedDirectionCancellation

/-- Recursive nonreversal is the usual adjacent-pair chain condition. -/
theorem hasNoImmediateReversal_iff_isChain
    (directions : List AxisDirection) :
    HasNoImmediateReversal directions ↔
      directions.IsChain fun first second =>
        second ≠ first.opposite := by
  induction directions using List.twoStepInduction with
  | nil | singleton =>
      simp [HasNoImmediateReversal]
  | cons_cons first second rest _ induction =>
      simp only [HasNoImmediateReversal,
        List.isChain_cons_cons, induction second]

/-- A duplicate-free unit-step point route cannot immediately retrace its
preceding edge. -/
theorem point_hasNoImmediateReversal_of_nodup_unitSteps
    (points : List Cell)
    (nodup : points.Nodup)
    (unitSteps : points.IsChain AxisDirection.IsUnitAxisStep) :
    AxisDirection.HasNoImmediateReversal points := by
  induction points using List.twoStepInduction with
  | nil | singleton =>
      simp [AxisDirection.HasNoImmediateReversal]
  | cons_cons first second rest _ induction =>
      cases rest with
      | nil =>
          simp [AxisDirection.HasNoImmediateReversal]
      | cons third rest =>
          have unitParts := List.isChain_cons_cons.mp unitSteps
          have tailUnitParts := List.isChain_cons_cons.mp unitParts.2
          have tailNodup : (second :: third :: rest).Nodup :=
            (List.nodup_cons.mp nodup).2
          constructor
          · intro reversal
            rcases unitParts.1 with
              ⟨incoming, incomingGenuine, secondEq⟩
            rcases tailUnitParts.1 with
              ⟨outgoing, outgoingGenuine, thirdEq⟩
            have incomingDirection :
                AxisDirection.between first second = incoming := by
              rw [secondEq]
              exact AxisDirection.between_add_step
                first incomingGenuine
            have outgoingDirection :
                AxisDirection.between second third = outgoing := by
              rw [thirdEq]
              exact AxisDirection.between_add_step
                second outgoingGenuine
            rw [incomingDirection, outgoingDirection] at reversal
            have outgoingEq : outgoing = incoming.opposite :=
              reversal
            subst outgoing
            have returnEq :=
              AxisDirection.add_opposite_step_add_step first
                (AxisDirection.opposite_isGenuine incomingGenuine)
            simp only [AxisDirection.opposite_opposite] at returnEq
            have thirdEqFirst : third = first := by
              rw [thirdEq, secondEq, returnEq]
            have firstNotMem := (List.nodup_cons.mp nodup).1
            apply firstNotMem
            simp [thirdEqFirst]
          · exact induction second tailNodup unitParts.2

/-- Point-level absence of immediate reversal transfers verbatim to the
consecutive direction word. -/
theorem routeStepDirections_hasNoImmediateReversal
    (points : List Cell)
    (noReversal : AxisDirection.HasNoImmediateReversal points) :
    HasNoImmediateReversal (Gadget.routeStepDirections points) := by
  induction points using List.twoStepInduction with
  | nil | singleton =>
      simp [Gadget.routeStepDirections, HasNoImmediateReversal]
  | cons_cons first second rest _ induction =>
      cases rest with
      | nil =>
          simp [Gadget.routeStepDirections, HasNoImmediateReversal]
      | cons third rest =>
          simp only [Gadget.routeStepDirections]
          change
            AxisDirection.between second third ≠
                (AxisDirection.between first second).opposite ∧
              HasNoImmediateReversal
                (AxisDirection.between second third ::
                  Gadget.routeStepDirections (third :: rest))
          refine ⟨noReversal.1, ?_⟩
          simpa [Gadget.routeStepDirections] using
            induction second noReversal.2

/-- Every simple orthogonal polyline has a nonreversing complete
unit-subdivision direction word. -/
theorem unitSubdivisionDirections_hasNoImmediateReversal
    (points : List Cell)
    (orthogonal : PeriodicOrthocrossing.OrthogonalPolyline points)
    (simple : LocalIncidenceDrawing.RouteIsSimple points) :
    HasNoImmediateReversal
      (Gadget.unitSubdivisionDirections points) := by
  let subdivided := AxisDirection.unitSubdividePolyline points
  have subdividedNodup : subdivided.Nodup := by
    exact AxisDirection.unitSubdividePolyline_nodup orthogonal simple
  have subdividedUnitSteps :
      subdivided.IsChain AxisDirection.IsUnitAxisStep := by
    exact AxisDirection.unitSubdividePolyline_unitSteps orthogonal
  have pointNoReversal :=
    point_hasNoImmediateReversal_of_nodup_unitSteps
      subdivided subdividedNodup subdividedUnitSteps
  have directionNoReversal :=
    routeStepDirections_hasNoImmediateReversal
      subdivided pointNoReversal
  rw [← Gadget.unitSubdivisionDirections_eq_routeStepDirections_of_unitSteps
      subdivided subdividedUnitSteps,
    Gadget.unitSubdivisionDirections_unitSubdividePolyline
      points orthogonal] at directionNoReversal
  exact directionNoReversal

/-- Initial and final slices of a nonreversing direction word remain
nonreversing. -/
theorem HasNoImmediateReversal.take
    {directions : List AxisDirection}
    (noReversal : HasNoImmediateReversal directions)
    (count : Nat) :
    HasNoImmediateReversal (directions.take count) := by
  induction count generalizing directions with
  | zero => trivial
  | succ count induction =>
      cases directions with
      | nil => trivial
      | cons first rest =>
          cases count with
          | zero => trivial
          | succ count =>
              cases rest with
              | nil => trivial
              | cons second rest =>
                  exact ⟨noReversal.1,
                    induction noReversal.2⟩

theorem HasNoImmediateReversal.drop
    {directions : List AxisDirection}
    (noReversal : HasNoImmediateReversal directions)
    (count : Nat) :
    HasNoImmediateReversal (directions.drop count) := by
  induction count generalizing directions with
  | zero => simpa using noReversal
  | succ count induction =>
      cases directions with
      | nil => trivial
      | cons first rest =>
          apply induction
          cases rest with
          | nil => trivial
          | cons second rest => exact noReversal.2

/-- The single newly adjacent pair at an append boundary is compatible in
every nonreversing combined word. -/
theorem compatibleHead_of_append
    (kept directions : List AxisDirection)
    (direction : AxisDirection)
    (keptLast : kept.getLast? = some direction)
    (noReversal : HasNoImmediateReversal (kept ++ directions)) :
    CompatibleHead direction directions := by
  cases directions with
  | nil => trivial
  | cons next rest =>
      have chain :=
        (hasNoImmediateReversal_iff_isChain
          (kept ++ next :: rest)).mp noReversal
      have boundary := (List.isChain_append.mp chain).2.2
      exact boundary direction (by simp [keptLast]) next (by simp)

end BoundedDelimitedDirectionCancellation
end LeanTrominoes
