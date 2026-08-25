/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordGuardedPairMergePairSemantics

/-! # Semantic output of guarded adjacent-word merging -/

namespace LeanTrominoes.DelimitedBinaryWordGuardedPairMerge

open DelimitedBinaryWords
open LightweightFiniteStateTransducer

/-- Semantic adjacent-word merging is exactly pairwise merging on a flattened
list of explicit word pairs. -/
@[simp] theorem mergeWords_componentWords
    (pairs : List (List Bool × List Bool)) :
    mergeWords (componentWords pairs).words = (mergedWords pairs).words := by
  induction pairs with
  | nil => rfl
  | cons pair pairs induction =>
      rcases pair with ⟨first, second⟩
      simp only [componentWords, mergedWords, List.flatMap_cons,
        List.map_cons]
      rw [show [first, second] ++
          pairs.flatMap (fun pair => [pair.1, pair.2]) =
            first :: second ::
              pairs.flatMap (fun pair => [pair.1, pair.2]) by rfl]
      simp only [mergeWords, List.cons.injEq, true_and]
      exact induction

/-- The physical transducer implements semantic adjacent-word merging on
every delimiter-encoded word list, including an odd final word. -/
@[simp] theorem tokens_encode_words : ∀ words : List (List Bool),
    tokens (DelimitedBinaryWords.encode ⟨words⟩) =
      DelimitedBinaryWords.encode ⟨mergeWords words⟩
  | [] => by rfl
  | [first] => by
      cases first with
      | nil => rfl
      | cons guard bits =>
          unfold tokens LightweightFiniteStateTransducer.output
            DelimitedBinaryWords.encode
          simp only [List.flatMap_cons, List.flatMap_nil,
            List.append_nil, mergeWords, wordTokens, List.map_cons,
            List.cons_append, scan, transition]
          rw [scan_firstBody_bits_wordEnd]
          simp [scan, finish]
  | first :: second :: words => by
      have induction := tokens_encode_words words
      unfold tokens LightweightFiniteStateTransducer.output at induction ⊢
      unfold DelimitedBinaryWords.encode at induction ⊢
      simp only [List.flatMap_cons, mergeWords]
      rw [← List.append_assoc (wordTokens first)]
      rw [scan_pair]
      simp only
      rw [List.append_assoc, induction]

/-- Merging an even stream containing exactly two component words per value
produces exactly one word per value. -/
theorem mergeWords_length_of_length_eq_twice
    (words : List (List Bool)) (count : Nat)
    (lengthEq : words.length = 2 * count) :
    (mergeWords words).length = count := by
  induction count generalizing words with
  | zero =>
      have wordsNil : words = [] :=
        List.eq_nil_of_length_eq_zero (by omega)
      subst words
      rfl
  | succ count induction =>
      cases words with
      | nil =>
          have impossible : False := by
            simp at lengthEq
          exact impossible.elim
      | cons first words =>
          cases words with
          | nil =>
              have impossible : False := by
                simp at lengthEq
                omega
              exact impossible.elim
          | cons second words =>
              simp only [mergeWords, List.length_cons]
              rw [induction words (by simp at lengthEq ⊢; omega)]

end LeanTrominoes.DelimitedBinaryWordGuardedPairMerge
