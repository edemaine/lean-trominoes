/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.StableOccurrenceRanksPartition
import LeanTrominoes.StableOccurrenceRankCandidateKeyNodup

/-! # Stable key lookup respects the complete equality partition -/

namespace LeanTrominoes.StableOccurrenceRanks

variable {First Second : Type*} [DecidableEq First] [DecidableEq Second]

private theorem idxsOf_eq_findIdxs_equalityRow (values : List First) (value : First) :
    values.idxsOf value = (equalityRow values value).findIdxs id := by
  simp only [List.idxsOf, equalityRow, List.findIdxs_map, Function.comp_def, id_eq]
  congr 1
  funext other
  simp only [Bool.beq_eq_decide_eq, eq_comm]

/-- Corresponding values have exactly the same ordered presentation indices. -/
theorem idxsOf_eq_of_partition
    (first : List First) (second : List Second) (lengths : first.length = second.length)
    (partition : ∀ (i j : Nat) (hi : i < first.length) (hj : j < first.length),
      first[i] = first[j] ↔ second[i]'(by omega) = second[j]'(by omega))
    (index : Nat) (indexLt : index < first.length) :
    first.idxsOf first[index] = second.idxsOf (second[index]'(by omega)) := by
  rw [idxsOf_eq_findIdxs_equalityRow, idxsOf_eq_findIdxs_equalityRow,
    equalityRow_eq_of_partition first second lengths partition index indexLt]

/-- A bounded numeric stable-key query selects the same presentation index
as the corresponding value's actual occurrence list. -/
theorem candidateKeys_idxOf_rank_of_partition
    (values : List Nat) (atoms : List Second) (lengths : values.length = atoms.length)
    (partition : ∀ (i j : Nat) (hi : i < values.length) (hj : j < values.length),
      values[i] = values[j] ↔ atoms[i]'(by omega) = atoms[j]'(by omega))
    (countLe : ∀ value ∈ values, values.count value ≤ 3)
    (index : Nat) (indexLt : index < values.length) (rank : Nat)
    (rankLt : rank < atoms.count (atoms[index]'(by omega))) :
    (candidateKeys values).idxOf (values[index] * 3 + rank) =
      (atoms.idxsOf (atoms[index]'(by omega))).getD rank 0 := by
  have counts := count_eq_of_partition values atoms lengths partition index indexLt
  have numericRankLt : rank < values.count values[index] := by rw [counts]; exact rankLt
  rw [candidateKeys_idxOf_rank values countLe values[index] rank numericRankLt,
    idxsOf_eq_of_partition values atoms lengths partition index indexLt]

end LeanTrominoes.StableOccurrenceRanks
