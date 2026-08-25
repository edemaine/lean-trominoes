/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairSelectorData
import LeanTrominoes.FiniteStateTransducerSemantics

/-! # Semantics of adjacent binary-word pair selection -/

namespace LeanTrominoes.DelimitedBinaryWordPairSelector

open DelimitedBinaryWords
open FiniteStateTransducer

theorem scan_bits_wordEnd (side : Side) (control : Control)
    (bits : List Bool) (suffix : List Token) :
    scan (transition side) control
        (bits.map Token.bit ++ .wordEnd :: suffix) =
      let next := advance control .wordEnd
      let rest := scan (transition side) next suffix
      (rest.1,
        (if selected side control then
          bits.map Token.bit ++ [.wordEnd]
        else []) ++ rest.2) := by
  induction bits with
  | nil =>
      cases side <;> cases control <;>
        simp [scan, transition, advance, selected]
  | cons bit bits induction =>
      cases side <;> cases control <;>
        simp [scan, transition, advance, selected, induction,
          List.append_assoc]

theorem scan_wordTokens (side : Side) (control : Control)
    (word : List Bool) (suffix : List Token) :
    scan (transition side) control (wordTokens word ++ suffix) =
      let next := advance control .wordEnd
      let rest := scan (transition side) next suffix
      (rest.1,
        (if selected side control then wordTokens word else []) ++
          rest.2) := by
  unfold wordTokens
  cases side <;> cases control <;>
    simp [scan, transition, advance, selected, scan_bits_wordEnd,
      List.append_assoc]

theorem scan_pair (side : Side) (first second : List Bool)
    (suffix : List Token) :
    scan (transition side) .first
        (wordTokens first ++ wordTokens second ++ suffix) =
      let rest := scan (transition side) .first suffix
      (rest.1, wordTokens (select side (first, second)) ++ rest.2) := by
  rw [List.append_assoc]
  rw [scan_wordTokens]
  simp only [advance, selected]
  rw [scan_wordTokens]
  cases side <;> simp [select, selected, advance]

/-- Scanning a flattened explicit pair stream returns to the first-word
state and emits exactly its selected words. -/
theorem scan_encode_componentWords (side : Side)
    (pairs : List (List Bool × List Bool)) :
    scan (transition side) .first
        (DelimitedBinaryWords.encode
          (DelimitedBinaryWordGuardedPairMerge.componentWords pairs)) =
      (.first, DelimitedBinaryWords.encode (selectedWords side pairs)) := by
  induction pairs with
  | nil => rfl
  | cons pair pairs induction =>
      rcases pair with ⟨first, second⟩
      unfold DelimitedBinaryWordGuardedPairMerge.componentWords
        selectedWords DelimitedBinaryWords.encode at induction ⊢
      simp only [List.map_cons, List.flatMap_cons]
      rw [List.flatMap_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [scan_pair]
      simp only
      rw [induction]

/-- Selecting one side of an explicit pair stream emits exactly one complete
word for every pair. -/
@[simp] theorem tokens_encode_componentWords (side : Side)
    (pairs : List (List Bool × List Bool)) :
    tokens side
        (DelimitedBinaryWords.encode
          (DelimitedBinaryWordGuardedPairMerge.componentWords pairs)) =
      DelimitedBinaryWords.encode (selectedWords side pairs) := by
  unfold tokens FiniteStateTransducer.output
  rw [scan_encode_componentWords]
  simp [finish]

end LeanTrominoes.DelimitedBinaryWordPairSelector
