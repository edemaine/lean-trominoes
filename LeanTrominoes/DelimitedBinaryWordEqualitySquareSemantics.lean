/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordEqualitySquareData
import LeanTrominoes.LastRepresentativeEqualityRowsSemantics
import LeanTrominoes.ListSplitLengthsFlatMapFixed

/-! # Semantics of square binary-word equality rows -/

namespace LeanTrominoes.DelimitedBinaryWordEqualitySquare

@[simp] theorem squareInput_side
    (input : DelimitedBinaryWords.Input) :
    (squareInput input).side = input.words.length := by
  unfold BoolSquareRows.Input.side squareInput
  rw [equalityBits_length, Nat.sqrt_eq']

/-- Recovering rows from the flat square gives exactly the semantic equality
row of every input word, in presentation order. -/
theorem rows_words (input : DelimitedBinaryWords.Input) :
    (rows input).words =
      LastRepresentativeEqualityRows.equalityRows input.words := by
  unfold rows BoolSquareRows.Input.delimitedRows BoolSquareRows.Input.rows
    BoolSquareRows.Input.sizes
  rw [squareInput_side]
  unfold squareInput LastRepresentativeEqualityRows.equalityRows
    LastRepresentativeEqualityRows.equalityRow
  change
    (List.replicate input.words.length input.words.length).splitLengths
        (equalityBits input) =
      input.words.map fun first =>
        input.words.map fun second => decide (first = second)
  rw [equalityBits_eq_flatMap]
  exact List.replicate_splitLengths_flatMap_of_length_eq
    input.words
    (fun first => input.words.map fun second => decide (first = second))
    input.words.length
    (by intro; simp)

/-- Structure-level version of exact square-row recovery. -/
theorem rows_eq (input : DelimitedBinaryWords.Input) :
    rows input =
      ⟨LastRepresentativeEqualityRows.equalityRows input.words⟩ := by
  cases inputRows : rows input with
  | mk words =>
      have wordsEq := rows_words input
      rw [inputRows] at wordsEq
      cases wordsEq
      rfl

end LeanTrominoes.DelimitedBinaryWordEqualitySquare
