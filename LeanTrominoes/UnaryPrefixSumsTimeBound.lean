/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.UnaryPrefixSumsFieldsTimeBound
import LeanTrominoes.UnaryPrefixSumsLengthBounds

/-! # Quadratic clock bound for unary prefix sums -/

namespace LeanTrominoes
namespace UnaryPrefixSumsMachine

theorem totalTime_le (values : List Nat) :
    totalTime values ≤
      5 * ((UnaryFieldEncoderMachine.unaryFields values).length + 1) ^ 2 := by
  let size := (UnaryFieldEncoderMachine.unaryFields values).length
  have outputBound := outputWord_length_le values
  have outputBound' :
      (outputWord values).length ≤ size * (size + 1) := by
    simpa [size] using outputBound
  have fieldsBound := fieldsTime_zero_le values
  have fieldsBound' :
      fieldsTime 0 values ≤ size * (3 * size + 4) := by
    simpa [size] using fieldsBound
  have sizeEq : size = values.sum + values.length := by
    simp [size]
  have sumBound : values.sum ≤ size := by
    omega
  unfold totalTime
  nlinarith [Nat.zero_le size]

end UnaryPrefixSumsMachine
end LeanTrominoes
