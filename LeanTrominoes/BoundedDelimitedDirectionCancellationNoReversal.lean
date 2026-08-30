/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoundedDelimitedDirectionCancellationData
import LeanTrominoes.DelimitedRouteJoinSemantics

/-! # Bounded cancellation preserves nonreversing direction words -/

namespace LeanTrominoes
namespace BoundedDelimitedDirectionCancellation

/-- Adjacent directions never point immediately back along the preceding
unit step. -/
def HasNoImmediateReversal : List AxisDirection → Prop
  | first :: second :: rest =>
      second ≠ first.opposite ∧
        HasNoImmediateReversal (second :: rest)
  | _ => True

def CompatibleHead (direction : AxisDirection) :
    List AxisDirection → Prop
  | [] => True
  | next :: _ => next ≠ direction.opposite

theorem buffered_increment
    (direction : AxisDirection) (count : Count)
    (positive : 0 < count.val)
    (notFull : count.val ≠ bufferCapacity) :
    buffered direction (count + 1) =
      buffered direction count ++ [.direction direction] := by
  native_decide +revert

theorem direction_cons_buffered_full
    (direction : AxisDirection) (count : Count)
    (full : count.val = bufferCapacity) :
    .direction direction :: buffered direction count =
      buffered direction count ++ [.direction direction] := by
  native_decide +revert

@[simp] theorem buffered_one (direction : AxisDirection) :
    buffered direction one = [.direction direction] := by
  native_decide +revert

theorem increment_positive
    (count : Count) (positive : 0 < count.val)
    (notFull : count.val ≠ bufferCapacity) :
    0 < (count + 1).val := by
  native_decide +revert

/-- Starting with a nonempty buffered run, a compatible nonreversing tail
is emitted unchanged when its route delimiter arrives. -/
theorem scan_run_of_noImmediateReversal
    (direction : AxisDirection) (count : Count)
    (positive : 0 < count.val)
    (directions : List AxisDirection)
    (boundary : CompatibleHead direction directions)
    (noReversal : HasNoImmediateReversal directions) :
    FiniteStateTransducer.scan transition (.run direction count)
        (directions.map (fun direction =>
          (.direction direction : Token)) ++ [.routeEnd]) =
      (.empty,
        buffered direction count ++
          directions.map (fun direction =>
            (.direction direction : Token)) ++ [.routeEnd]) := by
  induction directions generalizing direction count with
  | nil =>
      simp [FiniteStateTransducer.scan, transition]
  | cons next rest induction =>
      have nextNotReverse : next ≠ direction.opposite := by
        simpa [CompatibleHead] using boundary
      have restBoundary : CompatibleHead next rest := by
        cases rest with
        | nil => trivial
        | cons following rest =>
            exact noReversal.1
      have restNoReversal : HasNoImmediateReversal rest := by
        cases rest with
        | nil => trivial
        | cons following rest =>
            exact noReversal.2
      by_cases same : next = direction
      · subst next
        by_cases full : count.val = bufferCapacity
        · have step :
              transition (.run direction count) (.direction direction) =
                (.run direction count, [.direction direction]) := by
            simp [transition, full, bufferCapacity]
          simp only [List.map_cons, List.cons_append,
            FiniteStateTransducer.scan, step]
          rw [induction direction count positive restBoundary
            restNoReversal]
          simp only [List.nil_append, List.cons_append,
            List.append_assoc]
          congr 1
          rw [← List.cons_append]
          rw [direction_cons_buffered_full direction count full]
          simp [List.append_assoc]
        · have step :
              transition (.run direction count) (.direction direction) =
                (.run direction (count + 1), []) := by
            simp [transition, Nat.ne_of_gt positive, full]
          have incrementPositive : 0 < (count + 1).val :=
            increment_positive count positive full
          simp only [List.map_cons, List.cons_append,
            FiniteStateTransducer.scan, step, List.nil_append]
          rw [induction direction (count + 1) incrementPositive
            restBoundary restNoReversal]
          rw [buffered_increment direction count positive full]
          simp [List.append_assoc]
      · have step :
            transition (.run direction count) (.direction next) =
              (.run next one, buffered direction count) := by
          simp [transition, Nat.ne_of_gt positive, same, nextNotReverse]
        simp only [List.map_cons, List.cons_append,
          FiniteStateTransducer.scan, step]
        rw [induction next one (by decide) restBoundary restNoReversal]
        simp [List.append_assoc]

/-- On a complete delimited word with no immediate reversal, the bounded
canceller is the identity. -/
theorem output_delimited_eq_of_noImmediateReversal
    (directions : List AxisDirection)
    (noReversal : HasNoImmediateReversal directions) :
    output (DelimitedRouteJoin.delimited directions) =
      DelimitedRouteJoin.delimited directions := by
  cases directions with
  | nil =>
      simp [output, DelimitedRouteJoin.delimited,
        FiniteStateTransducer.output, FiniteStateTransducer.scan,
        transition, finish]
  | cons direction rest =>
      have boundary : CompatibleHead direction rest := by
        cases rest with
        | nil => trivial
        | cons next rest => exact noReversal.1
      have restNoReversal : HasNoImmediateReversal rest := by
        cases rest with
        | nil => trivial
        | cons next rest => exact noReversal.2
      unfold output DelimitedRouteJoin.delimited
        FiniteStateTransducer.output
      simp only [List.map_cons, List.cons_append,
        FiniteStateTransducer.scan, transition]
      rw [scan_run_of_noImmediateReversal direction one
        (by decide) rest boundary restNoReversal]
      simp [finish]

/-- The scan-level form of the identity theorem, before the empty finalizer
is applied. -/
theorem scan_empty_of_noImmediateReversal
    (directions : List AxisDirection)
    (noReversal : HasNoImmediateReversal directions) :
    FiniteStateTransducer.scan transition .empty
        (directions.map (fun direction =>
          (.direction direction : Token)) ++ [.routeEnd]) =
      (.empty,
        directions.map (fun direction =>
          (.direction direction : Token)) ++ [.routeEnd]) := by
  cases directions with
  | nil =>
      simp [FiniteStateTransducer.scan, transition]
  | cons direction rest =>
      have boundary : CompatibleHead direction rest := by
        cases rest with
        | nil => trivial
        | cons next rest => exact noReversal.1
      have restNoReversal : HasNoImmediateReversal rest := by
        cases rest with
        | nil => trivial
        | cons next rest => exact noReversal.2
      simp only [List.map_cons, List.cons_append,
        FiniteStateTransducer.scan, transition]
      rw [scan_run_of_noImmediateReversal direction one
        (by decide) rest boundary restNoReversal]
      simp

end BoundedDelimitedDirectionCancellation
end LeanTrominoes
