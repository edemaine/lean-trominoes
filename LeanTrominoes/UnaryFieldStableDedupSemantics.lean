/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordRepresentativeValueLookupSemantics
import LeanTrominoes.UnaryFieldStableDedupCompiler

/-! # Semantics of stable unary-field deduplication -/

namespace LeanTrominoes.UnaryFieldStableDedup

private theorem word_injective :
    Function.Injective UnaryFieldBinaryWords.word := by
  intro first second equal
  have lengths := congrArg List.length equal
  simpa [UnaryFieldBinaryWords.word] using lengths

/-- The representative lookup is exactly ordinary stable list
deduplication. -/
@[simp] theorem values_eq_dedup (source : List Nat) :
    values source = source.dedup := by
  unfold values
  have sourceAsLengths :
      source = (UnaryFieldBinaryWords.words source).words.map List.length := by
    change source = (source.map UnaryFieldBinaryWords.word).map List.length
    rw [List.map_map]
    change source = source.map fun value =>
      (UnaryFieldBinaryWords.word value).length
    simp [UnaryFieldBinaryWords.word]
  calc
    DelimitedBinaryWordRepresentativeValueLookup.selectedValues
          (UnaryFieldBinaryWords.words source) source =
        DelimitedBinaryWordRepresentativeValueLookup.selectedValues
          (UnaryFieldBinaryWords.words source)
          ((UnaryFieldBinaryWords.words source).words.map List.length) := by
      rw [← sourceAsLengths]
    _ = (UnaryFieldBinaryWords.words source).words.dedup.map List.length :=
      DelimitedBinaryWordRepresentativeValueLookup.selectedValues_map_eq_dedup_map
        _ _
    _ = source.dedup := by
      unfold UnaryFieldBinaryWords.words
      rw [List.dedup_map_of_injective word_injective]
      rw [List.map_map]
      change source.dedup.map (fun value =>
        (UnaryFieldBinaryWords.word value).length) = source.dedup
      simp [UnaryFieldBinaryWords.word]

end LeanTrominoes.UnaryFieldStableDedup
