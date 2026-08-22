/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupInput

/-! # Length bounds for last-true unary lookup -/

namespace LeanTrominoes
namespace LastTrueUnaryValueLookupMachine

@[simp] theorem encode_length (input : Input) :
    (encode input).length =
      (DelimitedBinaryWords.encode ⟨input.rows⟩).length +
        ((UnaryFieldEncoderMachine.unaryFields input.values).length + 1) := by
  simp [encode, SeparatedProductEncoding.encode_length]

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

theorem lookupAux_le (candidate : Nat) {row : List Bool}
    {values : List Nat} (valid : RowValid row values) :
    lookupAux candidate row values ≤ candidate + values.sum := by
  induction valid generalizing candidate with
  | nil => simp [lookupAux]
  | @cons bit value bits values valid induction =>
      cases bit with
      | false =>
          have rest := induction candidate
          simp only [lookupAux, List.sum_cons]
          omega
      | true =>
          have rest := induction value
          simp only [lookupAux, List.sum_cons]
          omega

theorem lookup_le_sum {row : List Bool} {values : List Nat}
    (valid : RowValid row values) :
    lookup row values ≤ values.sum := by
  simpa [lookup] using lookupAux_le 0 valid

theorem lookups_sum_le {rows : List (List Bool)} {values : List Nat}
    (valid : RowsValid values rows) :
    (lookups rows values).sum ≤ rows.length * values.sum := by
  induction valid with
  | nil => simp [lookups]
  | @cons row rows rowValid rest induction =>
      have head := lookup_le_sum rowValid
      simp only [lookups, List.map_cons, List.sum_cons, List.length_cons]
      calc
        lookup row values + (lookups rows values).sum ≤
            values.sum + rows.length * values.sum :=
          Nat.add_le_add head induction
        _ = (rows.length + 1) * values.sum := by ring

theorem outputEncoding_length_le_product (input : Input) :
    (outputEncoding input).length ≤
      input.rows.length * (input.values.sum + 1) := by
  have sumBound := lookups_sum_le input.valid
  have outputLength :
      (outputEncoding input).length =
        (lookups input.rows input.values).sum + input.rows.length := by
    simp [outputEncoding, lookups]
  rw [outputLength]
  calc
    (lookups input.rows input.values).sum + input.rows.length ≤
        input.rows.length * input.values.sum + input.rows.length :=
      Nat.add_le_add_right sumBound input.rows.length
    _ = input.rows.length * (input.values.sum + 1) := by ring

theorem outputEncoding_length_le_square (input : Input) :
    (outputEncoding input).length ≤ (encode input).length ^ 2 := by
  let inputLength := (encode input).length
  have outputBound := outputEncoding_length_le_product input
  have rowCountBound : input.rows.length ≤ inputLength := by
    have rowsBound := rows_length_le_encode_length input.rows
    simp [inputLength] at rowsBound ⊢
    exact rowsBound.trans (Nat.le_add_right _ _)
  have valueBound : input.values.sum + 1 ≤ inputLength := by
    simp [inputLength]
    omega
  calc
    (outputEncoding input).length ≤
        input.rows.length * (input.values.sum + 1) := outputBound
    _ ≤ inputLength * inputLength :=
      Nat.mul_le_mul rowCountBound valueBound
    _ = (encode input).length ^ 2 := by simp [inputLength, pow_two]

end LastTrueUnaryValueLookupMachine
end LeanTrominoes
