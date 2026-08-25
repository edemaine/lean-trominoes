/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryFieldPairPresenceCompiler

/-! # Semantics of unary-field row and column presence -/

namespace LeanTrominoes
namespace UnaryFieldPairPresence

def valuePresent : Side → Nat → Nat → Bool
  | .first, first, _ => decide (0 < first)
  | .second, _, second => decide (0 < second)

theorem fieldBits_eq_flatMap (side : Side) (values : List Nat) :
    fieldBits side values =
      values.flatMap fun first =>
        values.map fun second => valuePresent side first second := by
  unfold fieldBits bits
    DelimitedBinaryWordPairProductMachine.pairs
    UnaryFieldBinaryWords.words
  rw [List.map_flatMap, List.flatMap_map]
  apply List.flatMap_congr
  intro first _firstMember
  simp only [List.map_map]
  apply List.map_congr_left
  intro second _secondMember
  cases side with
  | first =>
      by_cases zero : first = 0
      · simp [present, valuePresent, UnaryFieldBinaryWords.word, zero]
      · have positive : 0 < first := Nat.pos_of_ne_zero zero
        simp [present, valuePresent, UnaryFieldBinaryWords.word,
          zero, positive]
  | second =>
      by_cases zero : second = 0
      · simp [present, valuePresent, UnaryFieldBinaryWords.word, zero]
      · have positive : 0 < second := Nat.pos_of_ne_zero zero
        simp [present, valuePresent, UnaryFieldBinaryWords.word,
          zero, positive]

end UnaryFieldPairPresence
end LeanTrominoes
