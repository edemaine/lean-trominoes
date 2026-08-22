/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupOneRowExecution
import LeanTrominoes.LastTrueUnaryValueLookupLengthBounds

/-! # Local time bounds for last-true unary lookup -/

namespace LeanTrominoes
namespace LastTrueUnaryValueLookupMachine

theorem bitsTime_le (candidate : Nat) {row : List Bool}
    {values : List Nat} (valid : RowValid row values) :
    bitsTime candidate row values ≤
      candidate + 4 * values.sum + 5 * values.length + 1 := by
  induction valid generalizing candidate with
  | nil => simp [bitsTime]
  | @cons bit value bits values valid induction =>
      cases bit with
      | false =>
          have rest := induction candidate
          simp only [bitsTime, List.sum_cons, List.length_cons]
          omega
      | true =>
          have rest := induction value
          simp only [bitsTime, List.sum_cons, List.length_cons]
          omega

theorem rowTime_le {row : List Bool} {values : List Nat}
    (valid : RowValid row values) :
    rowTime row values ≤
      8 * ((UnaryFieldEncoderMachine.unaryFields values).length + 1) := by
  have bitsBound := bitsTime_le 0 valid
  have lookupBound := lookup_le_sum valid
  unfold rowTime
  rw [UnaryFieldEncoderMachine.unaryFields_length]
  omega

end LastTrueUnaryValueLookupMachine
end LeanTrominoes
