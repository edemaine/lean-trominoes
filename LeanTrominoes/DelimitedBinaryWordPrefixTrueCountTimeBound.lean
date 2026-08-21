/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.DelimitedBinaryWordPrefixTrueCountLengthBounds
import LeanTrominoes.DelimitedBinaryWordPrefixTrueCountRowsTimeBound

/-! # Quadratic clock bound for row-prefix true counts -/

namespace LeanTrominoes
namespace DelimitedBinaryWordPrefixTrueCountMachine

theorem totalTime_le (rows : List (List Bool)) :
    totalTime rows ≤
      7 * ((DelimitedBinaryWords.encode ⟨rows⟩).length + 1) ^ 2 := by
  let size := (DelimitedBinaryWords.encode ⟨rows⟩).length
  have rowCountBound := rows_length_le_encode_length rows
  have rowCountBound' : rows.length ≤ size := by
    simpa [size] using rowCountBound
  have outputBound := outputWord_length_le rows
  have outputBound' :
      (outputWord rows).length ≤ size * (size + 1) := by
    simpa [size] using outputBound
  have processingBound := rowsTime_le 0 rows
  have processingBound' :
      rowsTime 0 rows ≤ 5 * size * (size + 1) := by
    have initial :
        rowsTime 0 rows ≤ 5 * rows.length * (size + 1) := by
      simpa [size] using processingBound
    exact initial.trans
      (Nat.mul_le_mul_right (size + 1)
        (Nat.mul_le_mul_left 5 rowCountBound'))
  unfold totalTime
  nlinarith [Nat.zero_le size]

end DelimitedBinaryWordPrefixTrueCountMachine
end LeanTrominoes
