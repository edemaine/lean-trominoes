/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteAlphabetKeyedValueLookupUniqueSemantics
import LeanTrominoes.UnaryKeyedValueLookupUniqueSemantics

/-! # Aligned lookup against a canonical range column -/

namespace LeanTrominoes

/-- A numeric aligned lookup whose candidate values are the canonical index
range returns the key's presentation index. -/
theorem UnaryKeyedValueLookup.alignedDatum_range
    (keys : List Nat) (key : Nat) (member : key ∈ keys) :
    UnaryKeyedValueLookup.alignedDatum
        keys (List.range keys.length) key =
      keys.idxOf key := by
  unfold UnaryKeyedValueLookup.alignedDatum
  have indexLt : keys.idxOf key < keys.length :=
    List.idxOf_lt_length_iff.mpr member
  have rangeLt : keys.idxOf key < (List.range keys.length).length := by
    simpa using indexLt
  rw [List.getD_eq_getElem _ _ rangeLt]
  exact List.getElem_range rangeLt

/-- Finite aligned lookup is ordinary total lookup at the numeric aligned
index returned by the canonical range column. -/
theorem FiniteAlphabetKeyedValueLookup.alignedDatum_eq_rangeIndex
    {Value : Type} [Fintype Value] [Inhabited Value]
    (keys : List Nat) (values : List Value) (key : Nat)
    (member : key ∈ keys) :
    FiniteAlphabetKeyedValueLookup.alignedDatum keys values key =
      values.getD
        (UnaryKeyedValueLookup.alignedDatum
          keys (List.range keys.length) key) default := by
  rw [UnaryKeyedValueLookup.alignedDatum_range keys key member]
  rfl

end LeanTrominoes
