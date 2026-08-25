/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoolSquareRowsInput
import LeanTrominoes.ListSplitLengthsFlatMapFixed

/-! # Recovering semantic rows from a flat promised square -/

namespace LeanTrominoes.BoolSquareRows

theorem delimitedRows_words_of_bits_eq_flatMap
    {Value : Type*} (input : Input) (values : List Value)
    (predicate : Value → Value → Bool)
    (sideEq : input.side = values.length)
    (bitsEq : input.bits =
      values.flatMap fun first => values.map (predicate first)) :
    input.delimitedRows.words =
      values.map fun first => values.map (predicate first) := by
  unfold Input.delimitedRows Input.rows Input.sizes
  rw [sideEq, bitsEq]
  exact List.replicate_splitLengths_flatMap_of_length_eq
    values (fun first => values.map (predicate first)) values.length
    (by intro; simp)

end LeanTrominoes.BoolSquareRows
