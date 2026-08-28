/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordTrailingBitPrefixData
import LeanTrominoes.FiniteStateTransducerSemantics

/-! # Exact semantics of trailing-bit word prefixing -/

namespace LeanTrominoes.DelimitedBinaryWordTrailingBitPrefix

open DelimitedBinaryWords

theorem scan_body_bits (trailingBit : Bool) (bits : List Bool) :
    FiniteStateTransducer.scan reverseTransition (.body trailingBit)
        (bits.map Token.bit) =
      (.body trailingBit, bits.map Token.bit) := by
  induction bits with
  | nil => rfl
  | cons bit bits induction =>
      simp [FiniteStateTransducer.scan, reverseTransition, induction]

/-- One reversed annotated word is changed into the reversal of its exact
prefixed form. -/
theorem scan_reversed_trailingWord
    (payload : List Bool) (trailingBit : Bool) :
    FiniteStateTransducer.scan reverseTransition .between
        (wordTokens (payload ++ [trailingBit])).reverse =
      (.between,
        (wordTokens (false :: trailingBit :: payload)).reverse) := by
  unfold wordTokens
  simp only [List.map_append, List.map_singleton, List.reverse_append,
    List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append]
  rw [FiniteStateTransducer.scan_append]
  simp only [FiniteStateTransducer.scan, reverseTransition]
  rw [← List.map_reverse, scan_body_bits]
  simp [List.map_reverse, List.append_assoc]

theorem scan_reversed_encode
    (items : List (List Bool × Bool)) :
    FiniteStateTransducer.scan reverseTransition .between
        (DelimitedBinaryWords.encode (trailingWords items)).reverse =
      (.between,
        (DelimitedBinaryWords.encode (prefixedWords items)).reverse) := by
  induction items with
  | nil => rfl
  | cons item items induction =>
      rcases item with ⟨payload, trailingBit⟩
      unfold trailingWords prefixedWords DelimitedBinaryWords.encode at induction ⊢
      simp only [List.map_cons, List.flatMap_cons, List.reverse_append]
      rw [FiniteStateTransducer.scan_append, induction]
      dsimp
      rw [scan_reversed_trailingWord]

/-- On every canonical annotated word stream, the physical transformation
moves the trailing bit behind the fixed leading `false`. -/
theorem tokens_encode (items : List (List Bool × Bool)) :
    tokens (DelimitedBinaryWords.encode (trailingWords items)) =
      DelimitedBinaryWords.encode (prefixedWords items) := by
  unfold tokens reversePass FiniteStateTransducer.output
  rw [scan_reversed_encode]
  simp [finish]

end LeanTrominoes.DelimitedBinaryWordTrailingBitPrefix
