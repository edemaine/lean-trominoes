/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.DelimitedBinaryWordPrefixTrueCountOneRowExecution

/-! # Local time bounds for row-prefix true counts -/

namespace LeanTrominoes
namespace DelimitedBinaryWordPrefixTrueCountMachine

@[simp] theorem wordTokens_length (row : List Bool) :
    (DelimitedBinaryWords.wordTokens row).length = row.length + 2 := by
  simp [DelimitedBinaryWords.wordTokens]

theorem rowScanTime_le (rowIndex : Nat) (row : List Bool) :
    rowScanTime rowIndex row ≤
      rowIndex + (DelimitedBinaryWords.wordTokens row).length := by
  rw [wordTokens_length]
  unfold rowScanTime
  split <;> omega

theorem oneRowTime_le (rowIndex : Nat) (row : List Bool) :
    oneRowTime rowIndex row ≤
      3 * (rowIndex + (DelimitedBinaryWords.wordTokens row).length) + 6 := by
  have scanBound := rowScanTime_le rowIndex row
  unfold oneRowTime
  omega

end DelimitedBinaryWordPrefixTrueCountMachine
end LeanTrominoes
