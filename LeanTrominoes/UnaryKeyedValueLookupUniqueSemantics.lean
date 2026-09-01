/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryKeyedValueLookupSemantics

/-! # Keyed lookup over a unique aligned candidate column -/

namespace LeanTrominoes.UnaryKeyedValueLookup

/-- Recover the candidate value at a key's unique presentation index. -/
def alignedDatum (candidateKeys candidateValues : List Nat)
    (key : Nat) : Nat :=
  candidateValues.getD (candidateKeys.idxOf key) 0

/-- A value column aligned with duplicate-free keys is exactly the keywise
map of its index-recovery function. -/
theorem candidateValues_eq_map_alignedDatum
    (candidateKeys candidateValues : List Nat)
    (aligned : candidateKeys.length = candidateValues.length)
    (keysNodup : candidateKeys.Nodup) :
    candidateValues =
      candidateKeys.map (alignedDatum candidateKeys candidateValues) := by
  apply List.ext_getElem (by simpa using aligned.symm)
  intro index valueIndexLt mappedIndexLt
  simp only [List.getElem_map]
  unfold alignedDatum
  rw [keysNodup.idxOf_getElem index (by simpa [aligned] using valueIndexLt)]
  exact (List.getD_eq_getElem candidateValues 0 valueIndexLt).symm

/-- A present key's recovered aligned datum belongs to the aligned candidate
value column. -/
theorem alignedDatum_mem_candidateValues
    (candidateKeys candidateValues : List Nat)
    (aligned : candidateKeys.length = candidateValues.length)
    (key : Nat) (keyMember : key ∈ candidateKeys) :
    alignedDatum candidateKeys candidateValues key ∈ candidateValues := by
  unfold alignedDatum
  have keyIndexLt : candidateKeys.idxOf key < candidateKeys.length :=
    List.idxOf_lt_length_iff.mpr keyMember
  have valueIndexLt : candidateKeys.idxOf key < candidateValues.length := by
    simpa [← aligned] using keyIndexLt
  rw [List.getD_eq_getElem candidateValues 0 valueIndexLt]
  exact List.getElem_mem _

/-- Index recovery at a duplicate-free aligned key returns its exact aligned
candidate value. -/
theorem alignedDatum_getElem
    (candidateKeys candidateValues : List Nat)
    (aligned : candidateKeys.length = candidateValues.length)
    (keysNodup : candidateKeys.Nodup)
    (index : Nat) (indexLt : index < candidateKeys.length) :
    alignedDatum candidateKeys candidateValues candidateKeys[index] =
      candidateValues[index]'(by simpa [← aligned] using indexLt) := by
  unfold alignedDatum
  rw [keysNodup.idxOf_getElem index indexLt]
  exact List.getD_eq_getElem candidateValues 0
    (by simpa [← aligned] using indexLt)

/-- With duplicate-free candidate keys, every present query selects the
candidate value at that key's unique aligned index. -/
theorem values_eq_map_alignedDatum
    (queries candidateKeys candidateValues : List Nat)
    (aligned : candidateKeys.length = candidateValues.length)
    (keysNodup : candidateKeys.Nodup)
    (present : ∀ query ∈ queries, query ∈ candidateKeys) :
    values queries candidateKeys candidateValues =
      queries.map (alignedDatum candidateKeys candidateValues) := by
  apply values_eq_map_datum queries candidateKeys candidateValues
    (alignedDatum candidateKeys candidateValues)
  · exact candidateValues_eq_map_alignedDatum
      candidateKeys candidateValues aligned keysNodup
  · exact present

end LeanTrominoes.UnaryKeyedValueLookup
