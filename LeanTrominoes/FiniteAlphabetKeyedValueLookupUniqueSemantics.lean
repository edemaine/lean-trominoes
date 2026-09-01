/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteAlphabetKeyedValueLookupSemantics

/-! # Finite keyed lookup over unique aligned candidates -/

namespace LeanTrominoes.FiniteAlphabetKeyedValueLookup

variable {Value : Type} [Fintype Value] [Inhabited Value]

/-- Recover the finite candidate value at a key's unique presentation
index. -/
def alignedDatum (candidateKeys : List Nat)
    (candidateValues : List Value) (key : Nat) : Value :=
  candidateValues.getD (candidateKeys.idxOf key) default

/-- A finite value column aligned with duplicate-free keys is its keywise
index-recovery map. -/
theorem candidateValues_eq_map_alignedDatum
    (candidateKeys : List Nat) (candidateValues : List Value)
    (aligned : candidateKeys.length = candidateValues.length)
    (keysNodup : candidateKeys.Nodup) :
    candidateValues =
      candidateKeys.map (alignedDatum candidateKeys candidateValues) := by
  apply List.ext_getElem (by simpa using aligned.symm)
  intro index valueIndexLt mappedIndexLt
  simp only [List.getElem_map]
  unfold alignedDatum
  rw [keysNodup.idxOf_getElem index (by simpa [aligned] using valueIndexLt)]
  exact (List.getD_eq_getElem candidateValues default valueIndexLt).symm

private theorem select_map_eq
    (query : Nat) (candidateKeys : List Nat) (datum : Nat → Value)
    (keysNodup : candidateKeys.Nodup) :
    (candidateKeys.map fun key => (key, datum key)).flatMap (fun candidate =>
        if query = candidate.1 then [candidate.2] else []) =
      (if query ∈ candidateKeys then [datum query] else []) := by
  induction candidateKeys with
  | nil => simp
  | cons key keys induction =>
      have ⟨keyNotMem, keysNodup'⟩ := List.nodup_cons.mp keysNodup
      by_cases same : query = key
      · subst key
        simp only [List.map_cons, List.flatMap_cons, if_pos rfl,
          List.mem_cons, true_or, if_true]
        rw [induction keysNodup', if_neg keyNotMem]
        rfl
      · simp only [List.map_cons, List.flatMap_cons, if_neg same,
          List.nil_append]
        rw [induction keysNodup']
        simp [same]

private theorem zip_map_same (candidateKeys : List Nat)
    (datum : Nat → Value) :
    candidateKeys.zip (candidateKeys.map datum) =
      candidateKeys.map fun key => (key, datum key) := by
  induction candidateKeys with
  | nil => rfl
  | cons key keys induction => simp [induction]

/-- With duplicate-free candidate keys, every present query selects the
finite candidate at its unique aligned position. -/
theorem values_eq_map_alignedDatum
    (queries candidateKeys : List Nat) (candidateValues : List Value)
    (aligned : candidateKeys.length = candidateValues.length)
    (keysNodup : candidateKeys.Nodup)
    (present : ∀ query ∈ queries, query ∈ candidateKeys) :
    values queries candidateKeys candidateValues =
      queries.map (alignedDatum candidateKeys candidateValues) := by
  rw [values_eq_expected _ _ _ aligned]
  unfold expected
  let datum := alignedDatum candidateKeys candidateValues
  change _ = queries.map datum
  have candidateValuesEq :
      candidateValues = candidateKeys.map datum :=
    candidateValues_eq_map_alignedDatum
      candidateKeys candidateValues aligned keysNodup
  have zipped :
      candidateKeys.zip (candidateKeys.map datum) =
        candidateKeys.map fun key => (key, datum key) :=
    zip_map_same candidateKeys datum
  rw [candidateValuesEq, zipped]
  calc
    _ = queries.flatMap fun query =>
          [datum query] := by
      apply List.flatMap_congr
      intro query queryMember
      rw [select_map_eq query candidateKeys
        datum keysNodup,
        if_pos (present query queryMember)]
    _ = queries.map datum := by
      rw [← List.map_eq_flatMap]

end LeanTrominoes.FiniteAlphabetKeyedValueLookup
