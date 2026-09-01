/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.StableOccurrenceRanks

/-! # Candidate keys from values and their stable occurrence ranks -/

namespace LeanTrominoes.StableOccurrenceRanks

variable {Value : Type*} [DecidableEq Value]

@[simp] theorem ranksAux_length (all remaining : List Value) (index : Nat) :
    (ranksAux all index remaining).length = remaining.length := by
  induction remaining generalizing index with
  | nil => rfl
  | cons value remaining induction => simp [ranksAux, induction]

@[simp] theorem ranks_length (values : List Value) :
    (ranks values).length = values.length := by
  simp [ranks]

theorem ranks_getElem? (values : List Value) (index : Nat) :
    (ranks values)[index]? =
      (values[index]?).map fun value =>
        (values.take index).count value := by
  rw [ranks_eq_map_zipIdx, List.getElem?_map, List.getElem?_zipIdx]
  simp [Function.comp_def]

private theorem count_take_findIdxNth
    (values : List Value) (value : Value) (rank : Nat)
    (rankLt : rank < values.count value) :
    (values.take
      (values.findIdxNth (fun other => other == value) rank)).count value =
        rank := by
  induction values generalizing rank with
  | nil => simp at rankLt
  | cons head values induction =>
      by_cases same : head = value
      · subst head
        cases rank with
        | zero =>
            rw [List.findIdxNth_cons_zero_of_pos (by simp)]
            rfl
        | succ rank =>
            have tailLt : rank < values.count value := by
              simpa using rankLt
            rw [List.findIdxNth_cons_succ_of_pos
                (p := fun other => other == value) (by simp),
              List.take_succ_cons]
            simp [induction rank tailLt]
      · have tailLt : rank < values.count value := by
          simpa [same] using rankLt
        have headFalse : (head == value) = false := by
          simp [same]
        rw [List.findIdxNth_cons_of_neg
            (p := fun other => other == value) headFalse,
          List.take_succ_cons]
        simp [same, induction rank tailLt]

/-- The number of equal values preceding the occurrence of rank `rank` is
exactly `rank`. -/
theorem count_take_getElem_idxsOf
    (values : List Value) (value : Value) (rank : Nat)
    (rankLt : rank < values.count value) :
    (values.take
      ((values.idxsOf value)[rank]'(by simpa using rankLt))).count value =
        rank := by
  have findLt :
      rank < (values.findIdxs (fun other => other == value)).length := by
    simpa only [List.length_findIdxs, ← List.count_eq_countP] using rankLt
  rw [show (values.idxsOf value)[rank]'(by simpa using rankLt) =
      (values.findIdxs (fun other => other == value))[rank]'findLt by rfl]
  rw [List.getElem_findIdxs_eq_findIdxNth]
  exact count_take_findIdxNth values value rank rankLt

/-- Numeric base-three keys for all stable ranked occurrences. -/
def candidateKeys (values : List Nat) : List Nat :=
  List.zipWith (fun value rank => value * 3 + rank)
    values (ranks values)

@[simp] theorem candidateKeys_length (values : List Nat) :
    (candidateKeys values).length = values.length := by
  simp [candidateKeys]

/-- Every rank below a value's multiplicity appears as one of its stable
candidate keys. -/
theorem candidateKey_mem_of_rank_lt_count
    (values : List Nat) (value rank : Nat)
    (rankLt : rank < values.count value) :
    value * 3 + rank ∈ candidateKeys values := by
  have findLt :
      rank < (values.findIdxs (fun other => other == value)).length := by
    simpa only [List.length_findIdxs, ← List.count_eq_countP] using rankLt
  let occurrenceIndex :=
    (values.findIdxs (fun other => other == value))[rank]'findLt
  have occurrenceIndexLt : occurrenceIndex < values.length := by
    exact List.getElem_findIdxs_lt findLt
  have valueAt : values[occurrenceIndex] = value := by
    have selected := List.getElem_getElem_findIdxs findLt
    simpa using selected
  have rankAt :
      (ranks values)[occurrenceIndex]'(by simpa using occurrenceIndexLt) =
        rank := by
    have rankIndexLt : occurrenceIndex < (ranks values).length := by
      simpa using occurrenceIndexLt
    have rankLookup :
        (ranks values)[occurrenceIndex]'rankIndexLt =
          (values.take occurrenceIndex).count values[occurrenceIndex] := by
      simpa only [List.getElem?_eq_getElem rankIndexLt,
        List.getElem?_eq_getElem occurrenceIndexLt, Option.map_some,
        Option.some.injEq] using ranks_getElem? values occurrenceIndex
    calc
      _ = (values.take occurrenceIndex).count values[occurrenceIndex] :=
        rankLookup
      _ = (values.take occurrenceIndex).count value := by rw [valueAt]
      _ = rank := by
        rw [show occurrenceIndex =
            (values.idxsOf value)[rank]'(by simpa using rankLt) by rfl]
        exact count_take_getElem_idxsOf values value rank rankLt
  have keyMember :
      (candidateKeys values)[occurrenceIndex]'(by
        simpa using occurrenceIndexLt) ∈ candidateKeys values :=
    List.getElem_mem _
  simpa [candidateKeys, occurrenceIndexLt, valueAt, rankAt] using keyMember

end LeanTrominoes.StableOccurrenceRanks
