/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastRepresentativeEqualityRowTokens
import LeanTrominoes.LastRepresentativeEqualityRowsLocalTimeBounds

/-! # Length bounds for last-representative filtering -/

namespace LeanTrominoes
namespace LastRepresentativeEqualityRowsMachine

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
          1 ≤ (DelimitedBinaryWords.wordTokens row).length := by simp
      omega

theorem tokensAux_length_le_encode_length (rowIndex : Nat)
    (rows : List (List Bool)) :
    (LastRepresentativeEqualityRowTokens.tokensAux rowIndex rows).length ≤
      (DelimitedBinaryWords.encode ⟨rows⟩).length := by
  induction rows generalizing rowIndex with
  | nil => simp
  | cons row rows induction =>
      simp only [DelimitedBinaryWords.encode, List.flatMap_cons,
        List.length_append]
      have tailBound (nextIndex : Nat) :
          (LastRepresentativeEqualityRowTokens.tokensAux
              nextIndex rows).length ≤
            (rows.flatMap DelimitedBinaryWords.wordTokens).length := by
        simpa only [DelimitedBinaryWords.encode] using induction nextIndex
      by_cases selectedEq :
          LastRepresentativeEqualityRows.selected rowIndex row = true
      · rw [LastRepresentativeEqualityRowTokens.tokensAux_cons_selected
          rowIndex row rows selectedEq, List.length_append]
        exact Nat.add_le_add_left (tailBound (rowIndex + 1)) _
      · have rejectedEq :
            LastRepresentativeEqualityRows.selected rowIndex row = false := by
          cases selected :
              LastRepresentativeEqualityRows.selected rowIndex row <;>
            simp_all
        rw [LastRepresentativeEqualityRowTokens.tokensAux_cons_rejected
          rowIndex row rows rejectedEq]
        exact (tailBound (rowIndex + 1)).trans
          (Nat.le_add_left _ _)

end LastRepresentativeEqualityRowsMachine
end LeanTrominoes
