/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairLengthComparisonExecution

/-! # Linear clock bound for delimited word-length comparison -/

namespace LeanTrominoes
namespace DelimitedBinaryWordPairLengthComparisonMachine

open DelimitedBinaryWordPairs

theorem compareTime_le (first second : List Bool) :
    compareTime first second ≤ first.length + second.length + 1 := by
  induction first generalizing second with
  | nil =>
      induction second with
      | nil => simp [compareTime]
      | cons bit second induction =>
          simp [compareTime] at induction ⊢
          omega
  | cons bit first induction =>
      cases second with
      | nil =>
          have bound := induction []
          simp [compareTime] at bound ⊢
          omega
      | cons secondBit second =>
          have bound := induction second
          simp [compareTime] at bound ⊢
          omega

@[simp] theorem pairTokens_length (first second : List Bool) :
    (pairTokens (first, second)).length =
      first.length + second.length + 3 := by
  simp [pairTokens]
  omega

theorem pairTime_le_tokens_length (first second : List Bool) :
    pairTime first second ≤ 2 * (pairTokens (first, second)).length := by
  have compared := compareTime_le first.reverse second.reverse
  simp only [List.length_reverse] at compared
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

@[simp] theorem pairResults_length
    (pairs : List (List Bool × List Bool)) :
    (pairResults pairs).length = pairs.length := by
  simp [pairResults]

theorem pairs_length_le_tokens_length
    (pairs : List (List Bool × List Bool)) :
    pairs.length ≤ (pairs.flatMap pairTokens).length := by
  induction pairs with
  | nil => simp
  | cons pair pairs induction =>
      rcases pair with ⟨first, second⟩
      simp only [List.length_cons, List.flatMap_cons, List.length_append,
        pairTokens_length]
      omega

theorem totalTime_le (input : Input) :
    totalTime input ≤ 3 * (encode input).length + 2 := by
  rcases input with ⟨pairs⟩
  have scanBound := pairsTime_le_tokens_length pairs
  have countBound := pairs_length_le_tokens_length pairs
  change pairsTime pairs +
      reverseTime
        (List.map (fun pair => compareLengths pair.1 pair.2) pairs).reverse ≤
    3 * (List.flatMap pairTokens pairs).length + 2
  simp only [reverseTime, List.length_reverse, List.length_map]
  omega

end DelimitedBinaryWordPairLengthComparisonMachine
end LeanTrominoes
