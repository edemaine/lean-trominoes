/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairBooleanFilterData

/-! # Length bounds for Boolean filtering of binary-word pairs -/

namespace LeanTrominoes.DelimitedBinaryWordPairBooleanFilter

theorem pairTokens_length_pos (pair : List Bool × List Bool) :
    1 ≤ (DelimitedBinaryWordPairs.pairTokens pair).length := by
  simp [DelimitedBinaryWordPairs.pairTokens]

theorem pairs_length_le_encode_length
    (pairs : List (List Bool × List Bool)) :
    pairs.length ≤
      (DelimitedBinaryWordPairs.encode ⟨pairs⟩).length := by
  induction pairs with
  | nil => simp [DelimitedBinaryWordPairs.encode]
  | cons pair pairs induction =>
      rw [show DelimitedBinaryWordPairs.encode ⟨pair :: pairs⟩ =
        DelimitedBinaryWordPairs.pairTokens pair ++
          DelimitedBinaryWordPairs.encode ⟨pairs⟩ by rfl]
      simp only [List.length_cons, List.length_append]
      have positive := pairTokens_length_pos pair
      omega

theorem selectedPairs_encode_length_le
    (controls : List Bool)
    (pairs : List (List Bool × List Bool)) :
    (DelimitedBinaryWordPairs.encode
        ⟨selectedPairs controls pairs⟩).length ≤
      (DelimitedBinaryWordPairs.encode ⟨pairs⟩).length := by
  induction controls generalizing pairs with
  | nil => simp [selectedPairs, DelimitedBinaryWordPairs.encode]
  | cons active controls induction =>
      cases pairs with
      | nil => simp [selectedPairs, DelimitedBinaryWordPairs.encode]
      | cons pair pairs =>
          cases active <;>
            simp only [selectedPairs, Bool.false_eq_true, ↓reduceIte,
              List.nil_append, List.singleton_append,
              DelimitedBinaryWordPairs.encode, List.flatMap_cons,
              List.length_append]
          · exact (induction pairs).trans (Nat.le_add_left _ _)
          · exact Nat.add_le_add_left (induction pairs) _

@[simp] theorem encodeInput_length (input : Input) :
    (encodeInput input).length = input.controls.length + 1 +
      (DelimitedBinaryWordPairs.encode ⟨input.pairs⟩).length := by
  simp [encodeInput, SeparatedProductEncoding.encode]
  omega

end LeanTrominoes.DelimitedBinaryWordPairBooleanFilter
