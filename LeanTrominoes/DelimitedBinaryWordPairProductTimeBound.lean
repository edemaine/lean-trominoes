/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairProductExecution

/-! # Quadratic clock bound for the binary-word ordered product -/

namespace LeanTrominoes

namespace DelimitedBinaryWordPairProductMachine

@[simp] theorem wordTokens_length (word : List Bool) :
    (DelimitedBinaryWords.wordTokens word).length = word.length + 2 := by
  simp [DelimitedBinaryWords.wordTokens]

@[simp] theorem pairTokens_length (first second : List Bool) :
    (DelimitedBinaryWordPairs.pairTokens (first, second)).length =
      first.length + second.length + 3 := by
  simp [DelimitedBinaryWordPairs.pairTokens]
  omega

theorem pairTime_le_token_product (first second : List Bool) :
    pairTime first second ≤
      (DelimitedBinaryWords.wordTokens first).length *
        (DelimitedBinaryWords.wordTokens second).length := by
  simp only [wordTokens_length]
  unfold pairTime
  simp only [Nat.add_mul, Nat.mul_add]
  omega

theorem pairTokens_length_le_token_product
    (first second : List Bool) :
    (DelimitedBinaryWordPairs.pairTokens (first, second)).length ≤
      (DelimitedBinaryWords.wordTokens first).length *
        (DelimitedBinaryWords.wordTokens second).length := by
  rw [pairTokens_length, wordTokens_length, wordTokens_length]
  simp only [Nat.add_mul, Nat.mul_add]
  omega

theorem rowTime_le (first : List Bool)
    (seconds : List (List Bool)) :
    rowTime first seconds ≤
      (DelimitedBinaryWords.wordTokens first).length *
        (seconds.flatMap DelimitedBinaryWords.wordTokens).length + 1 := by
  induction seconds with
  | nil => simp [rowTime]
  | cons second seconds induction =>
      have pairBound := pairTime_le_token_product first second
      simp only [rowTime, List.flatMap_cons, List.length_append]
      rw [Nat.mul_add]
      omega

theorem outerRowTime_le (first : List Bool)
    (seconds : List (List Bool)) :
    outerRowTime first seconds ≤
      4 * (DelimitedBinaryWords.wordTokens first).length *
        ((seconds.flatMap DelimitedBinaryWords.wordTokens).length + 1) := by
  have rowBound := rowTime_le first seconds
  simp only [wordTokens_length] at rowBound ⊢
  unfold outerRowTime
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc] at rowBound ⊢
  omega

theorem outerRowsTime_le (firsts seconds : List (List Bool)) :
    outerRowsTime seconds firsts ≤
      4 * (firsts.flatMap DelimitedBinaryWords.wordTokens).length *
        ((seconds.flatMap DelimitedBinaryWords.wordTokens).length + 1) := by
  induction firsts with
  | nil => simp [outerRowsTime]
  | cons first firsts induction =>
      have rowBound := outerRowTime_le first seconds
      simp only [outerRowsTime, List.flatMap_cons, List.length_append]
      calc
        outerRowTime first seconds + outerRowsTime seconds firsts ≤
            4 * (DelimitedBinaryWords.wordTokens first).length *
                ((seconds.flatMap
                  DelimitedBinaryWords.wordTokens).length + 1) +
              4 * (firsts.flatMap
                DelimitedBinaryWords.wordTokens).length *
                ((seconds.flatMap
                  DelimitedBinaryWords.wordTokens).length + 1) :=
          Nat.add_le_add rowBound induction
        _ = 4 *
              ((DelimitedBinaryWords.wordTokens first).length +
                (firsts.flatMap
                  DelimitedBinaryWords.wordTokens).length) *
              ((seconds.flatMap
                DelimitedBinaryWords.wordTokens).length + 1) := by
          simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
          omega

theorem rowTokens_length_le (first : List Bool)
    (seconds : List (List Bool)) :
    (rowTokens first seconds).length ≤
      (DelimitedBinaryWords.wordTokens first).length *
        (seconds.flatMap DelimitedBinaryWords.wordTokens).length := by
  induction seconds with
  | nil => simp [rowTokens]
  | cons second seconds induction =>
      have pairBound := pairTokens_length_le_token_product first second
      simp only [rowTokens] at induction ⊢
      simp only [List.flatMap_cons, List.length_append]
      rw [Nat.mul_add]
      omega

theorem productTokens_length_le (firsts seconds : List (List Bool)) :
    (productTokens firsts seconds).length ≤
      (firsts.flatMap DelimitedBinaryWords.wordTokens).length *
        (seconds.flatMap DelimitedBinaryWords.wordTokens).length := by
  induction firsts with
  | nil => simp [productTokens]
  | cons first firsts induction =>
      have rowBound := rowTokens_length_le first seconds
      simp only [productTokens] at induction ⊢
      simp only [List.flatMap_cons, List.length_append]
      rw [Nat.add_mul]
      omega

theorem totalTime_le (input : DelimitedBinaryWords.Input) :
    totalTime input ≤
      5 * (DelimitedBinaryWords.encode input).length ^ 2 +
        7 * (DelimitedBinaryWords.encode input).length + 5 := by
  rcases input with ⟨words⟩
  let size :=
    (words.flatMap DelimitedBinaryWords.wordTokens).length
  have rowsBound := outerRowsTime_le words words
  have outputBound := productTokens_length_le words words
  change outerRowsTime words words ≤ 4 * size * (size + 1)
    at rowsBound
  change (productTokens words words).length ≤ size * size
    at outputBound
  change finishTime
      (words.flatMap DelimitedBinaryWords.wordTokens)
      (productTokens words words).reverse +
        (outerRowsTime words words +
          setupTime (words.flatMap DelimitedBinaryWords.wordTokens)) ≤
    5 * size ^ 2 + 7 * size + 5
  dsimp [size] at rowsBound outputBound ⊢
  simp only [finishTime, setupTime, List.length_reverse]
  simp only [pow_two, Nat.mul_add, Nat.mul_assoc] at rowsBound ⊢
  omega

end DelimitedBinaryWordPairProductMachine
end LeanTrominoes
