/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoolSquareRowsInput
import LeanTrominoes.DelimitedBinaryWordPairProductMachine

/-! # Square equality matrices of delimited binary words -/

namespace LeanTrominoes.DelimitedBinaryWordEqualitySquare

/-- Row-major equality bits for the ordered square of a word list. -/
def equalityBits (input : DelimitedBinaryWords.Input) : List Bool :=
  DelimitedBinaryWordPairs.equalities
    (DelimitedBinaryWordPairProductMachine.pairs input)

theorem equalityBits_eq_flatMap
    (input : DelimitedBinaryWords.Input) :
    equalityBits input =
      input.words.flatMap fun first =>
        input.words.map fun second => decide (first = second) := by
  unfold equalityBits DelimitedBinaryWordPairs.equalities
    DelimitedBinaryWordPairProductMachine.pairs
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro first _firstMember
  simp [List.map_map, Function.comp_def]

@[simp] theorem equalityBits_length
    (input : DelimitedBinaryWords.Input) :
    (equalityBits input).length = input.words.length ^ 2 := by
  rw [equalityBits_eq_flatMap]
  simp [pow_two]

/-- The flat equality matrix equipped with its canonical square promise. -/
def squareInput (input : DelimitedBinaryWords.Input) :
    BoolSquareRows.Input where
  bits := equalityBits input
  square := by
    rw [equalityBits_length, Nat.sqrt_eq']

/-- Equality bits recovered into rows in the original word order. -/
def rows (input : DelimitedBinaryWords.Input) :
    DelimitedBinaryWords.Input :=
  (squareInput input).delimitedRows

end LeanTrominoes.DelimitedBinaryWordEqualitySquare
