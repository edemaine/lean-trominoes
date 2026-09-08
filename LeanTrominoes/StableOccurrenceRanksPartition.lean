/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.StableOccurrenceRankCandidateKeys

/-! # Stable ranks depend only on the equality partition of a list -/

namespace LeanTrominoes.StableOccurrenceRanks

variable {First Second : Type*} [DecidableEq First] [DecidableEq Second]

/-- Pointwise agreement of the equality partition identifies every complete
comparison row, without requiring a globally defined relabeling function. -/
theorem equalityRow_eq_of_partition
    (first : List First) (second : List Second) (lengths : first.length = second.length)
    (partition : ∀ (i j : Nat) (hi : i < first.length) (hj : j < first.length),
      first[i] = first[j] ↔ second[i]'(by omega) = second[j]'(by omega))
    (index : Nat) (indexLt : index < first.length) :
    equalityRow first first[index] = equalityRow second (second[index]'(by omega)) := by
  apply List.ext_getElem
  · simp only [equalityRow, List.length_map, lengths]
  · intro other firstLt secondLt
    simp only [equalityRow, List.getElem_map]
    have otherLt : other < first.length := by
      simpa only [equalityRow, List.length_map] using firstLt
    simp only [partition index other indexLt otherLt]

/-- Every prefix contains the same number of occurrences of corresponding
values when the two lists induce the same equality partition. -/
theorem count_take_eq_of_partition
    (first : List First) (second : List Second) (lengths : first.length = second.length)
    (partition : ∀ (i j : Nat) (hi : i < first.length) (hj : j < first.length),
      first[i] = first[j] ↔ second[i]'(by omega) = second[j]'(by omega))
    (index : Nat) (indexLt : index < first.length) (prefixLength : Nat) :
    (first.take prefixLength).count first[index] =
      (second.take prefixLength).count (second[index]'(by omega)) := by
  have rows := equalityRow_eq_of_partition first second lengths partition index indexLt
  have counts := congrArg (fun row => (row.take prefixLength).count true) rows
  simpa only [equalityRow_prefix_trueCount] using counts

/-- Corresponding values have the same total multiplicity. -/
theorem count_eq_of_partition
    (first : List First) (second : List Second) (lengths : first.length = second.length)
    (partition : ∀ (i j : Nat) (hi : i < first.length) (hj : j < first.length),
      first[i] = first[j] ↔ second[i]'(by omega) = second[j]'(by omega))
    (index : Nat) (indexLt : index < first.length) :
    first.count first[index] = second.count (second[index]'(by omega)) := by
  have counts := count_take_eq_of_partition first second lengths partition index indexLt first.length
  rw [List.take_length, lengths, List.take_length] at counts
  exact counts

/-- Stable occurrence ranks are unchanged by any pointwise correspondence
that preserves and reflects equality, even across different value types. -/
theorem ranks_eq_of_partition
    (first : List First) (second : List Second) (lengths : first.length = second.length)
    (partition : ∀ (i j : Nat) (hi : i < first.length) (hj : j < first.length),
      first[i] = first[j] ↔ second[i]'(by omega) = second[j]'(by omega)) :
    ranks first = ranks second := by
  apply List.ext_getElem?
  intro index
  rw [ranks_getElem?, ranks_getElem?]
  by_cases indexLt : index < first.length
  · have secondLt : index < second.length := by omega
    rw [List.getElem?_eq_getElem indexLt, List.getElem?_eq_getElem secondLt, Option.map_some, Option.map_some]
    exact congrArg some (count_take_eq_of_partition first second lengths partition index indexLt index)
  · have firstLe : first.length ≤ index := by omega
    have secondLe : second.length ≤ index := by omega
    simp only [List.getElem?_eq_none firstLe, List.getElem?_eq_none secondLe, Option.map_none]

/-- The complete per-occurrence multiplicity column depends only on the
list's equality partition. -/
theorem multiplicities_eq_of_partition
    (first : List First) (second : List Second) (lengths : first.length = second.length)
    (partition : ∀ (i j : Nat) (hi : i < first.length) (hj : j < first.length),
      first[i] = first[j] ↔ second[i]'(by omega) = second[j]'(by omega)) :
    first.map (fun value => first.count value) = second.map (fun value => second.count value) := by
  apply List.ext_getElem
  · simpa only [List.length_map] using lengths
  · intro index firstLt secondLt
    simp only [List.getElem_map]
    have indexLt : index < first.length := by simpa only [List.length_map] using firstLt
    exact count_eq_of_partition first second lengths partition index indexLt

end LeanTrominoes.StableOccurrenceRanks
