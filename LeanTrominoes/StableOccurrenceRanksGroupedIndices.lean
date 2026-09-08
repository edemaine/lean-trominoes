/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.StableOccurrenceRanksPartitionLookup
import LeanTrominoes.ListDedupMapInjectiveOn

/-! # Exact variable-major occurrence order depends only on equality classes -/

namespace LeanTrominoes.StableOccurrenceRanks

variable {First Second : Type*} [DecidableEq First] [DecidableEq Second]

/-- Presentation positions grouped in last-representative variable order,
then in increasing occurrence order within each variable. -/
def groupedIndices (values : List First) : List Nat :=
  values.dedup.flatMap fun value => values.idxsOf value

private theorem idxsOf_injective_on (values : List First)
    (first : First) (firstMember : first ∈ values)
    (second : First) (_secondMember : second ∈ values)
    (equal : values.idxsOf first = values.idxsOf second) : first = second := by
  obtain ⟨index, indexLt, indexEq⟩ := List.mem_iff_getElem.mp firstMember
  have firstIndex : index ∈ values.idxsOf first := by
    rw [List.mem_idxsOf_iff_getElem_pos indexLt]
    simpa only [beq_iff_eq] using indexEq
  rw [equal, List.mem_idxsOf_iff_getElem_pos indexLt] at firstIndex
  exact indexEq.symm.trans (beq_iff_eq.mp firstIndex)

/-- Deduplicating the complete per-position index blocks retains exactly
one block for each variable, in the source's own deduplication order. -/
theorem groupedIndices_eq_flatten_dedup (values : List First) :
    groupedIndices values = (values.map (fun value => values.idxsOf value)).dedup.flatten := by
  rw [List.dedup_map_of_injective_on _ _ (idxsOf_injective_on values)]
  rfl

/-- Equality-partition agreement preserves exact grouped occurrence order,
not merely a permutation of occurrence positions. -/
theorem groupedIndices_eq_of_partition
    (first : List First) (second : List Second) (lengths : first.length = second.length)
    (partition : ∀ (i j : Nat) (hi : i < first.length) (hj : j < first.length),
      first[i] = first[j] ↔ second[i]'(by omega) = second[j]'(by omega)) :
    groupedIndices first = groupedIndices second := by
  have blocks : first.map (fun value => first.idxsOf value) =
      second.map (fun value => second.idxsOf value) := by
    apply List.ext_getElem
    · simpa only [List.length_map] using lengths
    · intro index firstLt secondLt
      simp only [List.getElem_map]
      exact idxsOf_eq_of_partition first second lengths partition index
        (by simpa only [List.length_map] using firstLt)
  rw [groupedIndices_eq_flatten_dedup, groupedIndices_eq_flatten_dedup, blocks]

end LeanTrominoes.StableOccurrenceRanks
