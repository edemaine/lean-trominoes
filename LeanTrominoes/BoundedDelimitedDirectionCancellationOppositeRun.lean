/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoundedDelimitedDirectionCancellationNoReversal

/-! # Cancelling one bounded opposite-direction run -/

namespace LeanTrominoes
namespace BoundedDelimitedDirectionCancellation

def directionBlock (direction : AxisDirection) (amount : Count) :
    List Token :=
  List.replicate amount.val (.direction direction)

def overflow (count amount : Count) : Nat :=
  count.val + amount.val - bufferCapacity

def residual (count amount : Count) : Nat :=
  Nat.min bufferCapacity (count.val + amount.val) - amount.val

def residualCount (count amount : Count) : Count :=
  ⟨residual count amount,
    Nat.lt_succ_of_le
      (le_trans (Nat.sub_le _ _)
        (Nat.min_le_left _ _))⟩

def overflowBlock (direction : AxisDirection)
    (count amount : Count) : List Token :=
  List.replicate (overflow count amount) (.direction direction)

def afterCancellation (direction : AxisDirection)
    (count amount : Count) : Control :=
  if residual count amount = 0 then
    .empty
  else
    .run direction (residualCount count amount)

/-- The bounded finite calculation for extending a pending run and then
reading the same number of opposite directions. -/
theorem scan_directionBlock_opposite
    (direction : AxisDirection) (count amount : Count)
    (genuine : direction.IsGenuine)
    (positive : 0 < count.val) :
    FiniteStateTransducer.scan transition (.run direction count)
        (directionBlock direction amount ++
          directionBlock direction.opposite amount) =
      (afterCancellation direction count amount,
        overflowBlock direction count amount) := by
  native_decide +revert

/-- Output already emitted before the cancellation together with its
residual pending run is exactly the original pending run. -/
theorem overflowBlock_append_residual
    (direction : AxisDirection) (count amount : Count)
    (positive : 0 < count.val) :
    overflowBlock direction count amount ++
        buffered direction (residualCount count amount) =
      buffered direction count := by
  native_decide +revert

theorem residualCount_positive
    (count amount : Count)
    (residualPositive : residual count amount ≠ 0) :
    0 < (residualCount count amount).val := by
  exact Nat.pos_of_ne_zero residualPositive

/-- A bounded same/opposite block disappears before any compatible
nonreversing continuation. -/
theorem scan_run_directionBlock_opposite_of_noImmediateReversal
    (direction : AxisDirection) (count amount : Count)
    (genuine : direction.IsGenuine)
    (positive : 0 < count.val)
    (directions : List AxisDirection)
    (boundary : CompatibleHead direction directions)
    (noReversal : HasNoImmediateReversal directions) :
    FiniteStateTransducer.scan transition (.run direction count)
        (directionBlock direction amount ++
          directionBlock direction.opposite amount ++
          directions.map (fun direction =>
            (.direction direction : Token)) ++ [.routeEnd]) =
      (.empty,
        buffered direction count ++
          directions.map (fun direction =>
            (.direction direction : Token)) ++ [.routeEnd]) := by
  rw [show
      directionBlock direction amount ++
            directionBlock direction.opposite amount ++
            directions.map (fun direction =>
              (.direction direction : Token)) ++ [.routeEnd] =
        (directionBlock direction amount ++
          directionBlock direction.opposite amount) ++
          (directions.map (fun direction =>
            (.direction direction : Token)) ++ [.routeEnd]) by
      simp [List.append_assoc]]
  rw [FiniteStateTransducer.scan_append,
    scan_directionBlock_opposite direction count amount genuine positive]
  unfold afterCancellation
  by_cases residualZero : residual count amount = 0
  · simp only [if_pos residualZero]
    rw [scan_empty_of_noImmediateReversal directions noReversal]
    have residualNil :
        buffered direction (residualCount count amount) = [] := by
      simp [buffered, residualCount, residualZero]
    have materialized :=
      overflowBlock_append_residual direction count amount positive
    rw [residualNil, List.append_nil] at materialized
    simp [materialized, List.append_assoc]
  · simp only [if_neg residualZero]
    rw [scan_run_of_noImmediateReversal direction
        (residualCount count amount)
        (residualCount_positive count amount residualZero)
        directions boundary noReversal]
    congr 1
    simp only [List.append_assoc]
    calc
      overflowBlock direction count amount ++
            (buffered direction (residualCount count amount) ++
              (directions.map (fun direction =>
                (.direction direction : Token)) ++ [.routeEnd])) =
          (overflowBlock direction count amount ++
              buffered direction (residualCount count amount)) ++
            (directions.map (fun direction =>
              (.direction direction : Token)) ++ [.routeEnd]) := by
        exact (List.append_assoc _ _ _).symm
      _ = _ := by
        rw [overflowBlock_append_residual
          direction count amount positive]

/-- Once a kept prefix has been summarized by a pending final run, the
complete transducer erases one bounded out-and-back block and preserves the
kept prefix and compatible continuation. -/
theorem output_prefixScan_directionBlock_opposite
    (kept directions : List AxisDirection)
    (direction : AxisDirection) (count amount : Count)
    (emitted : List Token)
    (genuine : direction.IsGenuine)
    (positive : 0 < count.val)
    (prefixScan :
      FiniteStateTransducer.scan transition .empty
          (kept.map (fun direction =>
            (.direction direction : Token))) =
        (.run direction count, emitted))
    (prefixMaterialized :
      emitted ++ buffered direction count =
        kept.map (fun direction =>
          (.direction direction : Token)))
    (boundary : CompatibleHead direction directions)
    (noReversal : HasNoImmediateReversal directions) :
    output
        (kept.map (fun direction =>
            (.direction direction : Token)) ++
          directionBlock direction amount ++
          directionBlock direction.opposite amount ++
          directions.map (fun direction =>
            (.direction direction : Token)) ++ [.routeEnd]) =
      kept.map (fun direction =>
          (.direction direction : Token)) ++
        directions.map (fun direction =>
          (.direction direction : Token)) ++ [.routeEnd] := by
  unfold output FiniteStateTransducer.output
  rw [show
      kept.map (fun direction =>
            (.direction direction : Token)) ++
          directionBlock direction amount ++
          directionBlock direction.opposite amount ++
          directions.map (fun direction =>
            (.direction direction : Token)) ++ [.routeEnd] =
        kept.map (fun direction =>
            (.direction direction : Token)) ++
          (directionBlock direction amount ++
            directionBlock direction.opposite amount ++
            directions.map (fun direction =>
              (.direction direction : Token)) ++ [.routeEnd]) by
      simp [List.append_assoc]]
  rw [FiniteStateTransducer.scan_append, prefixScan]
  simp only
  rw [scan_run_directionBlock_opposite_of_noImmediateReversal
      direction count amount genuine positive directions boundary
      noReversal]
  simp only [finish, List.append_nil, List.append_assoc]
  calc
    emitted ++
          (buffered direction count ++
            (directions.map (fun direction =>
              (.direction direction : Token)) ++ [.routeEnd])) =
        (emitted ++ buffered direction count) ++
          (directions.map (fun direction =>
            (.direction direction : Token)) ++ [.routeEnd]) := by
      exact (List.append_assoc _ _ _).symm
    _ = _ := by rw [prefixMaterialized]

end BoundedDelimitedDirectionCancellation
end LeanTrominoes
