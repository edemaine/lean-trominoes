/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoundedDelimitedDirectionCancellationOppositeRun

/-! # Materializing nonreversing prefixes for bounded cancellation -/

namespace LeanTrominoes
namespace BoundedDelimitedDirectionCancellation

def lastDirection (initial : AxisDirection) :
    List AxisDirection → AxisDirection
  | [] => initial
  | next :: rest => lastDirection next rest

theorem getLast?_eq_lastDirection
    (initial : AxisDirection) (directions : List AxisDirection) :
    (initial :: directions).getLast? =
      some (lastDirection initial directions) := by
  induction directions generalizing initial with
  | nil => rfl
  | cons next rest induction =>
      simpa [lastDirection] using induction next

/-- Scanning a compatible nonreversing tail leaves a positive final run;
the emitted prefix followed by that pending run materializes the original
word exactly. -/
theorem scan_run_materialized_of_noImmediateReversal
    (direction : AxisDirection) (count : Count)
    (positive : 0 < count.val)
    (directions : List AxisDirection)
    (boundary : CompatibleHead direction directions)
    (noReversal : HasNoImmediateReversal directions) :
    ∃ (finalCount : Count) (emitted : List Token),
      0 < finalCount.val ∧
      FiniteStateTransducer.scan transition (.run direction count)
          (directions.map (fun direction =>
            (.direction direction : Token))) =
        (.run (lastDirection direction directions) finalCount, emitted) ∧
      emitted ++
          buffered (lastDirection direction directions) finalCount =
        buffered direction count ++
          directions.map (fun direction =>
            (.direction direction : Token)) := by
  induction directions generalizing direction count with
  | nil =>
      exact ⟨count, [], positive, rfl, by simp [lastDirection]⟩
  | cons next rest induction =>
      have nextNotReverse : next ≠ direction.opposite := by
        simpa [CompatibleHead] using boundary
      have restBoundary : CompatibleHead next rest := by
        cases rest with
        | nil => trivial
        | cons following rest => exact noReversal.1
      have restNoReversal : HasNoImmediateReversal rest := by
        cases rest with
        | nil => trivial
        | cons following rest => exact noReversal.2
      by_cases same : next = direction
      · subst next
        by_cases full : count.val = bufferCapacity
        · have step :
              transition (.run direction count) (.direction direction) =
                (.run direction count, [.direction direction]) := by
            simp [transition, full, bufferCapacity]
          rcases induction direction count positive restBoundary
              restNoReversal with
            ⟨finalCount, emitted, finalPositive, scanRest,
              materialized⟩
          refine ⟨finalCount, .direction direction :: emitted,
            finalPositive, ?_, ?_⟩
          · simp only [List.map_cons, FiniteStateTransducer.scan,
              step, scanRest, lastDirection, List.cons_append,
              List.nil_append]
          · simp only [lastDirection, List.cons_append]
            rw [materialized]
            rw [show
                .direction direction ::
                    (buffered direction count ++
                      rest.map (fun direction =>
                        (.direction direction : Token))) =
                  (.direction direction :: buffered direction count) ++
                    rest.map (fun direction =>
                      (.direction direction : Token)) by
                rfl]
            rw [direction_cons_buffered_full direction count full]
            simp [List.append_assoc]
        · have step :
              transition (.run direction count) (.direction direction) =
                (.run direction (count + 1), []) := by
            simp [transition, Nat.ne_of_gt positive, full]
          have incrementPositive : 0 < (count + 1).val :=
            increment_positive count positive full
          rcases induction direction (count + 1) incrementPositive
              restBoundary restNoReversal with
            ⟨finalCount, emitted, finalPositive, scanRest,
              materialized⟩
          refine ⟨finalCount, emitted, finalPositive, ?_, ?_⟩
          · simp only [List.map_cons, FiniteStateTransducer.scan,
              step, scanRest, lastDirection, List.nil_append]
          · simp only [lastDirection]
            rw [materialized,
              buffered_increment direction count positive full]
            simp [List.append_assoc]
      · have step :
            transition (.run direction count) (.direction next) =
              (.run next one, buffered direction count) := by
          simp [transition, Nat.ne_of_gt positive, same, nextNotReverse]
        rcases induction next one (by decide) restBoundary
            restNoReversal with
          ⟨finalCount, emitted, finalPositive, scanRest,
            materialized⟩
        refine ⟨finalCount, buffered direction count ++ emitted,
          finalPositive, ?_, ?_⟩
        · simp only [List.map_cons, FiniteStateTransducer.scan,
            step, scanRest, lastDirection]
        · simp only [lastDirection, List.append_assoc]
          rw [materialized, buffered_one]
          rfl

/-- A nonempty nonreversing word whose last direction is known has a scan
summary in precisely that final direction. -/
theorem exists_prefixScan_of_noImmediateReversal
    (directions : List AxisDirection) (finalDirection : AxisDirection)
    (nonempty : directions ≠ [])
    (last : directions.getLast? = some finalDirection)
    (noReversal : HasNoImmediateReversal directions) :
    ∃ (count : Count) (emitted : List Token),
      0 < count.val ∧
      FiniteStateTransducer.scan transition .empty
          (directions.map (fun direction =>
            (.direction direction : Token))) =
        (.run finalDirection count, emitted) ∧
      emitted ++ buffered finalDirection count =
        directions.map (fun direction =>
          (.direction direction : Token)) := by
  obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil nonempty
  have boundary : CompatibleHead first rest := by
    cases rest with
    | nil => trivial
    | cons next rest => exact noReversal.1
  have restNoReversal : HasNoImmediateReversal rest := by
    cases rest with
    | nil => trivial
    | cons next rest => exact noReversal.2
  rcases scan_run_materialized_of_noImmediateReversal
      first one (by decide) rest boundary restNoReversal with
    ⟨count, emitted, positive, scanRest, materialized⟩
  have finalEq : lastDirection first rest = finalDirection := by
    rw [getLast?_eq_lastDirection] at last
    exact Option.some.inj last
  subst finalDirection
  refine ⟨count, emitted, positive, ?_, ?_⟩
  · simp only [List.map_cons, FiniteStateTransducer.scan,
      transition, scanRest, List.nil_append]
  · simpa using materialized

/-- Declarative direction-list interface: remove a bounded constant run and
its reverse between a nonempty kept prefix and a compatible continuation. -/
theorem output_delimited_append_opposite_blocks
    (kept directions : List AxisDirection)
    (direction : AxisDirection) (amount : Count)
    (genuine : direction.IsGenuine)
    (keptNonempty : kept ≠ [])
    (keptLast : kept.getLast? = some direction)
    (keptNoReversal : HasNoImmediateReversal kept)
    (boundary : CompatibleHead direction directions)
    (noReversal : HasNoImmediateReversal directions) :
    output
        (DelimitedRouteJoin.delimited
          (kept ++ List.replicate amount.val direction ++
            List.replicate amount.val direction.opposite ++ directions)) =
      DelimitedRouteJoin.delimited (kept ++ directions) := by
  rcases exists_prefixScan_of_noImmediateReversal
      kept direction keptNonempty keptLast keptNoReversal with
    ⟨count, emitted, positive, prefixScan, materialized⟩
  have compiled := output_prefixScan_directionBlock_opposite
    kept directions direction count amount emitted genuine positive
    prefixScan materialized boundary noReversal
  simpa [DelimitedRouteJoin.delimited, directionBlock,
    List.map_append, List.map_replicate, List.append_assoc] using compiled

end BoundedDelimitedDirectionCancellation
end LeanTrominoes
