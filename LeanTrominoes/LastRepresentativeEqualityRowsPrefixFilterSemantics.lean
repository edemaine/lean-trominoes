/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastRepresentativeEqualityRowsPrefixFilter
import LeanTrominoes.LastRepresentativeEqualityRowsSemantics

/-! # Semantics of prefix-supported last-representative rows -/

namespace LeanTrominoes.LastRepresentativeEqualityRows

variable {Value : Type*} [DecidableEq Value]

/-- On an equality row, prefix support is exactly membership of the row's
value in the corresponding candidate prefix. -/
theorem meetsPrefix_equalityRow_append
    (base suffix : List Value) (value : Value) :
    meetsPrefix base.length
        (equalityRow (base ++ suffix) value) =
      decide (value ∈ base) := by
  unfold meetsPrefix equalityRow
  induction base with
  | nil => simp
  | cons head tail induction =>
      by_cases equal : value = head
      · subst head
        simp
      · simp [equal]

/-- Prefix filtering after last-representative selection is exactly stable
deduplication followed by membership filtering of the represented values. -/
theorem prefixSupportedRows_equalityRows
    (base suffix : List Value) :
    prefixSupportedRows base.length
        ⟨equalityRows (base ++ suffix)⟩ =
      ⟨(((base ++ suffix).dedup.filter fun value =>
          value ∈ base).map
        (equalityRow (base ++ suffix)))⟩ := by
  unfold prefixSupportedRows
  rw [rows_equalityRows]
  congr 1
  induction (base ++ suffix).dedup with
  | nil => rfl
  | cons value values induction =>
      by_cases member : value ∈ base
      · simp [meetsPrefix_equalityRow_append, member, induction]
      · simp [meetsPrefix_equalityRow_append, member, induction]

end LeanTrominoes.LastRepresentativeEqualityRows
