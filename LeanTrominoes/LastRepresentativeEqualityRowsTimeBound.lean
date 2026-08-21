/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastRepresentativeEqualityRowsExecution
import LeanTrominoes.LastRepresentativeEqualityRowsLengthBounds
import LeanTrominoes.LastRepresentativeEqualityRowsRowsTimeBound

/-! # Quadratic clock bound for last-representative filtering -/

namespace LeanTrominoes
namespace LastRepresentativeEqualityRowsMachine

theorem totalTime_le (input : DelimitedBinaryWords.Input) :
    totalTime input.words ≤
      5 * (DelimitedBinaryWords.encode input).length ^ 2 +
        7 * (DelimitedBinaryWords.encode input).length + 3 := by
  rcases input with ⟨rows⟩
  let size := (DelimitedBinaryWords.encode ⟨rows⟩).length
  let tokens := LastRepresentativeEqualityRowTokens.tokensAux 0 rows
  have rowCountBound := rows_length_le_encode_length rows
  have tokenBound := tokensAux_length_le_encode_length 0 rows
  have timeBound := rowsTime_le 0 rows
  have timeBound' :
      rowsTime 0 rows ≤ 5 * rows.length * (size + 1) := by
    simpa [size] using timeBound
  have timeBound'' :
      rowsTime 0 rows ≤ 5 * size * (size + 1) :=
    timeBound'.trans
      (Nat.mul_le_mul_right (size + 1)
        (Nat.mul_le_mul_left 5 (by simpa [size] using rowCountBound)))
  have cleanupBound :
      finalCleanupTime rows.length tokens ≤ 2 * size + 3 := by
    have rowCountBound' : rows.length ≤ size := by
      simpa [size] using rowCountBound
    have tokenBound' : tokens.length ≤ size := by
      simpa [tokens, size] using tokenBound
    simp only [finalCleanupTime]
    omega
  calc
    totalTime rows =
        finalCleanupTime rows.length tokens + rowsTime 0 rows := by
      rfl
    _ ≤ (2 * size + 3) + 5 * size * (size + 1) :=
      Nat.add_le_add cleanupBound timeBound''
    _ = 5 * size ^ 2 + 7 * size + 3 := by ring

end LastRepresentativeEqualityRowsMachine
end LeanTrominoes
