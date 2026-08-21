/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.UnaryPrefixSumsListExecution

/-! # Time bound for scanning unary prefix-sum fields -/

namespace LeanTrominoes
namespace UnaryPrefixSumsMachine

theorem fieldsTime_le (start : Nat) (values : List Nat) :
    fieldsTime start values ≤
      values.length * (3 * (start + values.sum) + 4) := by
  induction values generalizing start with
  | nil => simp [fieldsTime]
  | cons value values induction =>
      let budget := 3 * (start + (value + values.sum)) + 4
      have rest := induction (start + value)
      have rest' :
          fieldsTime (start + value) values ≤
            values.length * budget := by
        simpa [budget, Nat.add_assoc] using rest
      have head : 2 * start + value + 4 ≤ budget := by
        simp [budget]
        omega
      rw [fieldsTime]
      simp only [List.length_cons, List.sum_cons]
      calc
        fieldsTime (start + value) values +
            (2 * start + value + 4) ≤
          values.length * budget + budget :=
            Nat.add_le_add rest' head
        _ = (values.length + 1) * budget := by ring

theorem fieldsTime_zero_le (values : List Nat) :
    fieldsTime 0 values ≤
      (UnaryFieldEncoderMachine.unaryFields values).length *
        (3 * (UnaryFieldEncoderMachine.unaryFields values).length + 4) := by
  have bound := fieldsTime_le 0 values
  have encodingLength :
      (UnaryFieldEncoderMachine.unaryFields values).length =
        values.sum + values.length := by
    simp
  rw [encodingLength]
  have lengthLe : values.length ≤ values.sum + values.length := by
    omega
  have factorLe :
      3 * (0 + values.sum) + 4 ≤
        3 * (values.sum + values.length) + 4 := by
    omega
  exact bound.trans (Nat.mul_le_mul lengthLe factorLe)

end UnaryPrefixSumsMachine
end LeanTrominoes
