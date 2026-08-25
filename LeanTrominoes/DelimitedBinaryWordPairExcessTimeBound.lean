/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairExcessExecution

/-! # Linear clock bound for unary word-pair excesses -/

namespace LeanTrominoes
namespace DelimitedBinaryWordPairExcessMachine

open DelimitedBinaryWordPairs

theorem cancelTime_le (first second : List Bool) :
    cancelTime first second ≤ first.length + second.length + 1 := by
  induction first generalizing second with
  | nil =>
      cases second with
      | nil => simp [cancelTime]
      | cons bit second => simp [cancelTime, drainTime]; omega
  | cons bit first induction =>
      cases second with
      | nil => simp [cancelTime, drainTime]; omega
      | cons secondBit second =>
          have bound := induction second
          simp only [cancelTime, List.length_cons]
          omega

@[simp] theorem pairTokens_length (first second : List Bool) :
    (pairTokens (first, second)).length =
      first.length + second.length + 3 := by
  simp [pairTokens]
  omega

theorem pairTime_le_tokens_length (first second : List Bool) :
    pairTime first second ≤ 2 * (pairTokens (first, second)).length := by
  have cancelled := cancelTime_le first.reverse second.reverse
  simp only [List.length_reverse] at cancelled
  rw [pairTokens_length]
  unfold pairTime
  omega

theorem pairsTime_le_tokens_length
    (pairs : List (List Bool × List Bool)) :
    pairsTime pairs ≤ 2 * (pairs.flatMap pairTokens).length + 1 := by
  induction pairs with
  | nil => simp [pairsTime]
  | cons pair pairs induction =>
      rcases pair with ⟨first, second⟩
      have pairBound := pairTime_le_tokens_length first second
      simp only [pairsTime, List.flatMap_cons, List.length_append]
      omega

theorem excess_le_length_sum (keepFirst : Bool)
    (first second : List Bool) :
    excess keepFirst first second ≤ first.length + second.length := by
  cases keepFirst <;> simp [excess] <;> omega

theorem pairExcesses_sum_add_length_le_tokens_length (keepFirst : Bool)
    (pairs : List (List Bool × List Bool)) :
    (pairExcesses keepFirst pairs).sum +
        (pairExcesses keepFirst pairs).length ≤
      (pairs.flatMap pairTokens).length := by
  induction pairs with
  | nil => simp [pairExcesses]
  | cons pair pairs induction =>
      rcases pair with ⟨first, second⟩
      have headBound := excess_le_length_sum keepFirst first second
      rw [show pairExcesses keepFirst ((first, second) :: pairs) =
          excess keepFirst first second :: pairExcesses keepFirst pairs by
        rfl]
      rw [List.flatMap_cons]
      simp only [List.sum_cons, List.length_cons, List.length_append]
      rw [pairTokens_length]
      omega

theorem unaryFields_pairExcesses_length_le_tokens_length (keepFirst : Bool)
    (pairs : List (List Bool × List Bool)) :
    (UnaryFieldEncoderMachine.unaryFields
        (pairExcesses keepFirst pairs)).length ≤
      (pairs.flatMap pairTokens).length := by
  rw [UnaryFieldEncoderMachine.unaryFields_length]
  exact pairExcesses_sum_add_length_le_tokens_length keepFirst pairs

theorem totalTime_le (keepFirst : Bool) (input : Input) :
    totalTime keepFirst input ≤ 3 * (encode input).length + 2 := by
  rcases input with ⟨pairs⟩
  have scanBound := pairsTime_le_tokens_length pairs
  have outputBound :=
    unaryFields_pairExcesses_length_le_tokens_length keepFirst pairs
  change pairsTime pairs +
      reverseTime
        (UnaryFieldEncoderMachine.unaryFields
          (pairExcesses keepFirst pairs)).reverse ≤
    3 * (pairs.flatMap pairTokens).length + 2
  simp only [reverseTime, List.length_reverse]
  omega

end DelimitedBinaryWordPairExcessMachine
end LeanTrominoes
