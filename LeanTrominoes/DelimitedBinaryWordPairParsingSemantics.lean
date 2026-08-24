/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Basic
import LeanTrominoes.DelimitedBinaryWordPairParsingData

/-! # Correctness of delimiter-encoded binary-word pair parsing -/

namespace LeanTrominoes.DelimitedBinaryWordPairs

theorem parse_append (state : ParseState) (first second : List Token) :
    parse state (first ++ second) = parse (parse state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons token first induction =>
      simp only [List.cons_append, parse]
      exact induction (parseStep state token)

theorem parse_firstBits (pairs : List (List Bool × List Bool))
    (first firstReverse : List Bool) :
    parse (.first pairs firstReverse) (first.map .firstBit) =
      .first pairs (first.reverse ++ firstReverse) := by
  induction first generalizing firstReverse with
  | nil => simp [parse]
  | cons bit first induction =>
      simp only [List.map_cons, parse, parseStep]
      rw [induction]
      simp [List.reverse_cons, List.append_assoc]

theorem parse_secondBits (pairs : List (List Bool × List Bool))
    (first second secondReverse : List Bool) :
    parse (.second pairs first secondReverse) (second.map .secondBit) =
      .second pairs first (second.reverse ++ secondReverse) := by
  induction second generalizing secondReverse with
  | nil => simp [parse]
  | cons bit second induction =>
      simp only [List.map_cons, parse, parseStep]
      rw [induction]
      simp [List.reverse_cons, List.append_assoc]

theorem parse_pairTokens (pairs : List (List Bool × List Bool))
    (pair : List Bool × List Bool) :
    parse (.between pairs) (pairTokens pair) =
      .between (pair :: pairs) := by
  rcases pair with ⟨first, second⟩
  simp only [pairTokens, parse, parseStep]
  rw [parse_append, parse_firstBits]
  simp only [parse, parseStep]
  rw [parse_append, parse_secondBits]
  simp [parse, parseStep]

theorem parse_encodeAux (prior suffix : List (List Bool × List Bool)) :
    parse (.between prior) (suffix.flatMap pairTokens) =
      .between (suffix.reverse ++ prior) := by
  induction suffix generalizing prior with
  | nil => simp [parse]
  | cons pair suffix induction =>
      rw [List.flatMap_cons]
      rw [parse_append, parse_pairTokens]
      rw [induction]
      simp [List.reverse_cons, List.append_assoc]

@[simp] theorem decode_encode (input : Input) :
    decode (encode input) = some input := by
  rcases input with ⟨pairs⟩
  simp [decode, encode, parse_encodeAux]

end LeanTrominoes.DelimitedBinaryWordPairs
