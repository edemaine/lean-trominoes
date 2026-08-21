/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.DelimitedBinaryWordPrefixTrueCountExecution

/-! # Output-length bounds for row-prefix true counts -/

namespace LeanTrominoes
namespace DelimitedBinaryWordPrefixTrueCountMachine

theorem count_le_index (rowIndex : Nat) (row : List Bool) :
    DelimitedBinaryWordPrefixTrueCounts.count rowIndex row ≤ rowIndex := by
  calc
    DelimitedBinaryWordPrefixTrueCounts.count rowIndex row ≤
        (row.take rowIndex).length := List.count_le_length
    _ ≤ rowIndex := by simp

theorem countsAux_sum_le (rowIndex : Nat) (rows : List (List Bool)) :
    (DelimitedBinaryWordPrefixTrueCounts.countsAux rowIndex rows).sum ≤
      rows.length * (rowIndex + rows.length) := by
  induction rows generalizing rowIndex with
  | nil => simp
  | cons row rows induction =>
      let budget := rowIndex + (rows.length + 1)
      have head := count_le_index rowIndex row
      have head' :
          DelimitedBinaryWordPrefixTrueCounts.count rowIndex row ≤
            budget := head.trans (by simp [budget])
      have tail := induction (rowIndex + 1)
      have tail' :
          (DelimitedBinaryWordPrefixTrueCounts.countsAux
              (rowIndex + 1) rows).sum ≤
            rows.length * budget := by
        simpa [budget, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using tail
      simp only [DelimitedBinaryWordPrefixTrueCounts.countsAux,
        List.sum_cons, List.length_cons]
      calc
        DelimitedBinaryWordPrefixTrueCounts.count rowIndex row +
            (DelimitedBinaryWordPrefixTrueCounts.countsAux
              (rowIndex + 1) rows).sum ≤
          budget + rows.length * budget :=
            Nat.add_le_add head' tail'
        _ = (rows.length + 1) *
            (rowIndex + (rows.length + 1)) := by
          simp [budget]
          ring

theorem rows_length_le_encode_length (rows : List (List Bool)) :
    rows.length ≤ (DelimitedBinaryWords.encode ⟨rows⟩).length := by
  induction rows with
  | nil => simp [DelimitedBinaryWords.encode]
  | cons row rows induction =>
      simp only [DelimitedBinaryWords.encode, List.flatMap_cons,
        List.length_cons, List.length_append]
      have tailBound :
          rows.length ≤
            (rows.flatMap DelimitedBinaryWords.wordTokens).length := by
        simpa only [DelimitedBinaryWords.encode] using induction
      have rowTokenPos :
          1 ≤ (DelimitedBinaryWords.wordTokens row).length := by
        simp [DelimitedBinaryWords.wordTokens]
      omega

theorem outputWord_length_le (rows : List (List Bool)) :
    (outputWord rows).length ≤
      (DelimitedBinaryWords.encode ⟨rows⟩).length *
        ((DelimitedBinaryWords.encode ⟨rows⟩).length + 1) := by
  let counts := DelimitedBinaryWordPrefixTrueCounts.countsAux 0 rows
  let rowCount := rows.length
  let inputLength := (DelimitedBinaryWords.encode ⟨rows⟩).length
  have sumBound := countsAux_sum_le 0 rows
  have sumBound' : counts.sum ≤ rowCount * rowCount := by
    simpa [counts, rowCount] using sumBound
  have countsLength : counts.length = rowCount := by
    simp [counts, rowCount]
  have outputLength :
      (outputWord rows).length = counts.sum + rowCount := by
    simp [outputWord, counts, rowCount]
  have rowCountBound : rowCount ≤ inputLength := by
    simpa [rowCount, inputLength] using rows_length_le_encode_length rows
  rw [outputLength]
  calc
    counts.sum + rowCount ≤ rowCount * rowCount + rowCount :=
      Nat.add_le_add_right sumBound' rowCount
    _ = rowCount * (rowCount + 1) := by ring
    _ ≤ inputLength * (inputLength + 1) :=
      Nat.mul_le_mul rowCountBound (Nat.add_le_add_right rowCountBound 1)

end DelimitedBinaryWordPrefixTrueCountMachine
end LeanTrominoes
