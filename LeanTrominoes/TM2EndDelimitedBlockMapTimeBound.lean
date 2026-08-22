/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2EndDelimitedBlockMapTimePolynomial

/-! # Polynomial bound for the exact block-map recurrence -/

noncomputable section

namespace LeanTrominoes
namespace TM2EndDelimitedBlockMap

open Turing

section

variable {Source Target : Type}
variable {function : List Source → List Target}

theorem mapRunTime_le
    (inner : TM2ComputableInPolyTime id id function)
    (isEnd : Source → Bool) (limit : Nat) :
    ∀ (input blockReverse : List Source) (outputReverse : List Target),
      input.length + blockReverse.length ≤ limit →
      mapRunTime inner isEnd input blockReverse outputReverse ≤
        2 * outputReverse.length +
          (input.length + 1) * unitCost inner limit +
          blockReverse.length := by
  intro input
  induction input with
  | nil =>
      intro blockReverse outputReverse sizeBound
      have unitLarge := unitCost_three_le inner limit
      simp only [mapRunTime, List.length_nil, Nat.zero_add,
        Nat.one_mul]
      omega
  | cons symbol remaining induction =>
      intro blockReverse outputReverse sizeBound
      cases ends : isEnd symbol with
      | false =>
          have nextSize :
              remaining.length + (symbol :: blockReverse).length ≤
                limit := by
            simp only [List.length_cons] at sizeBound ⊢
            omega
          have restBound := induction (symbol :: blockReverse)
            outputReverse nextSize
          have unitLarge := unitCost_three_le inner limit
          rw [mapRunTime]
          simp only [ends, Bool.false_eq_true, ↓reduceIte]
          simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
            at restBound ⊢
          omega
      | true =>
          let block := (symbol :: blockReverse).reverse
          have blockLength : block.length = blockReverse.length + 1 := by
            simp [block]
          have blockBound : block.length ≤ limit := by
            simp only [List.length_cons] at sizeBound
            omega
          have nextSize : remaining.length + ([] : List Source).length ≤
              limit := by
            simp only [List.length_cons] at sizeBound
            simp
            omega
          have restBound := induction []
            ((function block).reverse ++ outputReverse) nextSize
          have blockCost := blockRunTime_with_output_le_unitCost
            inner block limit blockBound
          rw [mapRunTime]
          simp only [ends, ↓reduceIte]
          change mapRunTime inner isEnd remaining []
              ((function block).reverse ++ outputReverse) +
                (blockRunTime inner block + 2) ≤
            2 * outputReverse.length +
              ((remaining.length + 1) + 1) * unitCost inner limit +
              blockReverse.length
          simp only [List.length_append, List.length_reverse,
            List.length_nil, Nat.add_zero, Nat.add_mul, Nat.one_mul]
            at restBound ⊢
          omega

theorem initialMapRunTime_le_polynomial
    (inner : TM2ComputableInPolyTime id id function)
    (isEnd : Source → Bool) (input : List Source) :
    mapRunTime inner isEnd input [] [] ≤
      (mapTimePolynomial inner).eval input.length := by
  rw [mapTimePolynomial_eval]
  simpa using mapRunTime_le inner isEnd input.length input [] [] (by simp)

end

end TM2EndDelimitedBlockMap
end LeanTrominoes
