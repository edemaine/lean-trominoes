/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.UnaryPrefixSumsExecution

/-! # Length bounds for unary prefix sums -/

namespace LeanTrominoes
namespace UnaryPrefixSumsMachine

theorem startsAux_sum_le (start : Nat) (values : List Nat) :
    (PrefixSums.startsAux start values).sum ≤
      values.length * (start + values.sum) := by
  induction values generalizing start with
  | nil => simp [PrefixSums.startsAux]
  | cons value values induction =>
      have rest := induction (start + value)
      have rest' :
          (PrefixSums.startsAux (start + value) values).sum ≤
            values.length * (start + (value + values.sum)) := by
        simpa [Nat.add_assoc] using rest
      have startBound : start ≤ start + (value + values.sum) := by
        omega
      simp only [PrefixSums.startsAux, List.sum_cons, List.length_cons]
      calc
        start + (PrefixSums.startsAux (start + value) values).sum ≤
            (start + (value + values.sum)) +
              values.length * (start + (value + values.sum)) :=
          Nat.add_le_add startBound rest'
        _ = (values.length + 1) *
            (start + (value + values.sum)) := by ring

theorem outputWord_length_le (values : List Nat) :
    (outputWord values).length ≤
      (UnaryFieldEncoderMachine.unaryFields values).length *
        ((UnaryFieldEncoderMachine.unaryFields values).length + 1) := by
  have startsBound := startsAux_sum_le 0 values
  have startsBound' :
      (PrefixSums.starts values).sum ≤ values.length * values.sum := by
    simpa [PrefixSums.starts] using startsBound
  have inputLengthEq :
      (UnaryFieldEncoderMachine.unaryFields values).length =
        values.sum + values.length := by
    simp
  have outputLengthEq :
      (outputWord values).length =
        (PrefixSums.starts values).sum + values.length := by
    simp [outputWord]
  rw [outputLengthEq, inputLengthEq]
  calc
    (PrefixSums.starts values).sum + values.length ≤
        values.length * values.sum + values.length :=
      Nat.add_le_add_right startsBound' values.length
    _ = values.length * (values.sum + 1) := by ring
    _ ≤ (values.sum + values.length) *
        (values.sum + values.length + 1) := by
      exact Nat.mul_le_mul (by omega) (by omega)

end UnaryPrefixSumsMachine
end LeanTrominoes
