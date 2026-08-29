/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteUnitOffsets
import LeanTrominoes.ListLoopEraseAppend
import LeanTrominoes.OrthogonalPolylineLoopErasureJoin

/-! # Right localization of orthogonal-polyline loop erasure -/

namespace LeanTrominoes
namespace AxisDirection

open PeriodicOrthocrossing

/-- Subdividing one genuine unit step merely lists its two endpoints. -/
theorem unitSegmentPoints_eq_pair_of_unitAxisStep
    {first second : Cell}
    (unit : IsUnitAxisStep first second) :
    unitSegmentPoints first second = [first, second] := by
  rw [unitSegmentPoints]
  rw [Gadget.segmentLength_eq_one_of_unitAxisStep unit]
  have scaleZero (point : Cell) :
      Cell.scale (0 : Int) point = (0, 0) := by
    rcases point with ⟨x, y⟩
    simp [Cell.scale]
  have scaleOne (point : Cell) :
      Cell.scale (1 : Int) point = point := by
    rcases point with ⟨x, y⟩
    simp [Cell.scale]
  have addZero (point : Cell) :
      Cell.add point (0, 0) = point := by
    rcases point with ⟨x, y⟩
    simp [Cell.add]
  rw [show List.range 2 = [0, 1] by decide]
  simp only [List.map_cons, List.map_nil, Nat.cast_zero,
    Nat.cast_one, List.cons.injEq, and_true]
  constructor
  · rw [scaleZero, addZero]
  · rw [scaleOne]
    exact (add_between_step_eq_of_unitAxisStep unit).symm

/-- Ordered unit subdivision is idempotent on an already unit-step route. -/
theorem unitSubdividePolyline_eq_self_of_unitSteps
    {points : List Cell}
    (unitSteps : points.IsChain IsUnitAxisStep) :
    unitSubdividePolyline points = points := by
  induction points using List.twoStepInduction with
  | nil | singleton =>
      simp
  | cons_cons first second rest _ induction =>
      have firstUnit : IsUnitAxisStep first second :=
        (List.isChain_cons_cons.mp unitSteps).1
      have tailUnitSteps :
          (second :: rest).IsChain IsUnitAxisStep :=
        (List.isChain_cons_cons.mp unitSteps).2
      rw [unitSubdividePolyline,
        unitSegmentPoints_eq_pair_of_unitAxisStep firstUnit,
        induction second tailUnitSteps]
      simp [joinAtEndpoint]

/-- On a nonempty orthogonal route, the total normalizer is the proof-free
right-to-left loop eraser applied to ordered unit subdivision. -/
theorem normalizeOrthogonalPolyline_eq_listLoopErase
    {points : List Cell}
    (nonempty : points ≠ [])
    (orthogonal : OrthogonalPolyline points) :
    normalizeOrthogonalPolyline points =
      Computability.listLoopErase
        (unitSubdividePolyline points) := by
  rw [normalizeOrthogonalPolyline_eq_erase nonempty orthogonal,
    eraseOrthogonalLoops_eq_listLoopErase nonempty orthogonal]

/-- Normalizing the right route before an endpoint join does not change the
normalization of the combined route.  No simplicity or separation premise is
needed: this is a consequence of right-to-left loop erasure. -/
theorem normalizeOrthogonalPolyline_joinAtEndpoint_normalize_right
    {first second : List Cell}
    {boundary : Cell}
    (firstNonempty : first ≠ [])
    (secondNonempty : second ≠ [])
    (firstOrthogonal : OrthogonalPolyline first)
    (secondOrthogonal : OrthogonalPolyline second)
    (firstLast : first.getLast? = some boundary)
    (secondHead : second.head? = some boundary) :
    normalizeOrthogonalPolyline
        (joinAtEndpoint first second) =
      normalizeOrthogonalPolyline
        (joinAtEndpoint first
          (normalizeOrthogonalPolyline second)) := by
  let normalizedSecond := normalizeOrthogonalPolyline second
  have normalizedSecondNonempty : normalizedSecond ≠ [] :=
    normalizeOrthogonalPolyline_ne_nil
      secondNonempty secondOrthogonal
  have normalizedSecondOrthogonal :
      OrthogonalPolyline normalizedSecond :=
    normalizeOrthogonalPolyline_orthogonal
      secondNonempty secondOrthogonal
  have normalizedSecondHead :
      normalizedSecond.head? = some boundary := by
    simpa [normalizedSecond] using
      (normalizeOrthogonalPolyline_head?
        secondNonempty secondOrthogonal).trans secondHead
  have firstSubdividedLast :
      (unitSubdividePolyline first).getLast? =
        some boundary := by
    rw [unitSubdividePolyline_getLast?
      firstNonempty firstOrthogonal, firstLast]
  have secondSubdividedHead :
      (unitSubdividePolyline second).head? =
        some boundary := by
    rw [unitSubdividePolyline_head? secondNonempty, secondHead]
  have normalizedSecondEq :
      normalizedSecond =
        Computability.listLoopErase
          (unitSubdividePolyline second) := by
    exact normalizeOrthogonalPolyline_eq_listLoopErase
      secondNonempty secondOrthogonal
  have erasedSecondHead :
      (Computability.listLoopErase
        (unitSubdividePolyline second)).head? =
          some boundary := by
    rw [← normalizedSecondEq]
    exact normalizedSecondHead
  have normalizedSecondSubdivide :
      unitSubdividePolyline normalizedSecond =
        normalizedSecond :=
    unitSubdividePolyline_eq_self_of_unitSteps
      (normalizeOrthogonalPolyline_unitSteps
        secondNonempty secondOrthogonal)
  have joinedNonempty : joinAtEndpoint first second ≠ [] := by
    intro empty
    cases first with
    | nil => exact firstNonempty rfl
    | cons head tail => simp [joinAtEndpoint] at empty
  have joinedOrthogonal :
      OrthogonalPolyline (joinAtEndpoint first second) :=
    firstOrthogonal.joinAtEndpoint secondOrthogonal
      firstLast secondHead
  have normalizedJoinedNonempty :
      joinAtEndpoint first normalizedSecond ≠ [] := by
    intro empty
    cases first with
    | nil => exact firstNonempty rfl
    | cons head tail => simp [joinAtEndpoint] at empty
  have normalizedJoinedOrthogonal :
      OrthogonalPolyline
        (joinAtEndpoint first normalizedSecond) :=
    firstOrthogonal.joinAtEndpoint normalizedSecondOrthogonal
      firstLast normalizedSecondHead
  calc
    normalizeOrthogonalPolyline (joinAtEndpoint first second) =
        Computability.listLoopErase
          (unitSubdividePolyline
            (joinAtEndpoint first second)) :=
      normalizeOrthogonalPolyline_eq_listLoopErase
        joinedNonempty joinedOrthogonal
    _ = Computability.listLoopErase
          (joinAtEndpoint
            (unitSubdividePolyline first)
            (unitSubdividePolyline second)) := by
      rw [unitSubdividePolyline_joinAtEndpoint
        firstNonempty firstLast secondHead]
    _ = Computability.listLoopErase
          (joinAtEndpoint
            (unitSubdividePolyline first)
            (Computability.listLoopErase
              (unitSubdividePolyline second))) :=
      Computability.listLoopErase_joinAtEndpoint_right
        firstSubdividedLast secondSubdividedHead erasedSecondHead
    _ = Computability.listLoopErase
          (joinAtEndpoint
            (unitSubdividePolyline first) normalizedSecond) := by
      rw [normalizedSecondEq]
    _ = Computability.listLoopErase
          (unitSubdividePolyline
            (joinAtEndpoint first normalizedSecond)) := by
      rw [unitSubdividePolyline_joinAtEndpoint
        firstNonempty firstLast normalizedSecondHead,
        normalizedSecondSubdivide]
    _ = normalizeOrthogonalPolyline
          (joinAtEndpoint first normalizedSecond) := by
      symm
      exact normalizeOrthogonalPolyline_eq_listLoopErase
        normalizedJoinedNonempty normalizedJoinedOrthogonal

end AxisDirection
end LeanTrominoes
