/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2EndDelimitedBlockMapCleanupIndex

/-! # Decreasing measure for block-map cleanup -/

noncomputable section

namespace LeanTrominoes
namespace TM2EndDelimitedBlockMap

open scoped BigOperators

open Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

def innerPopulation (inner : FinTM2)
    (innerContents : ∀ stack, List (inner.Γ stack)) : Nat :=
  ∑ stack, (innerContents stack).length

def cleanupMeasure (inner : FinTM2)
    (position : Fin (Fintype.card inner.K + 1))
    (innerContents : ∀ stack, List (inner.Γ stack)) : Nat :=
  innerPopulation inner innerContents +
    (Fintype.card inner.K - position.val)

theorem innerPopulation_update_cons
    (inner : FinTM2)
    (innerContents : ∀ target, List (inner.Γ target))
    (stack : inner.K) (symbol : inner.Γ stack)
    (tail : List (inner.Γ stack))
    (contentsEq : innerContents stack = symbol :: tail) :
    innerPopulation inner (Function.update innerContents stack tail) + 1 =
      innerPopulation inner innerContents := by
  classical
  unfold innerPopulation
  let updated := Function.update innerContents stack tail
  calc
    (∑ target, (updated target).length) + 1 =
        ((∑ target ∈ Finset.univ.erase stack,
          (updated target).length) + (updated stack).length) + 1 := by
      congr 1
      exact (Finset.sum_erase_add _ _ (Finset.mem_univ stack)).symm
    _ = ((∑ target ∈ Finset.univ.erase stack,
          (innerContents target).length) + tail.length) + 1 := by
      congr 2
      · apply Finset.sum_congr rfl
        intro target member
        simp only [updated]
        rw [Function.update_of_ne (Finset.ne_of_mem_erase member)]
      · simp [updated]
    _ = (∑ target ∈ Finset.univ.erase stack,
          (innerContents target).length) + (symbol :: tail).length := by
      simp
      omega
    _ = ∑ target, (innerContents target).length := by
      rw [← contentsEq]
      exact Finset.sum_erase_add _ _ (Finset.mem_univ stack)

theorem cleanupMeasure_update_lt
    (inner : FinTM2)
    (position : Fin (Fintype.card inner.K + 1))
    (innerContents : ∀ target, List (inner.Γ target))
    (stack : inner.K) (symbol : inner.Γ stack)
    (tail : List (inner.Γ stack))
    (contentsEq : innerContents stack = symbol :: tail) :
    cleanupMeasure inner position
        (Function.update innerContents stack tail) <
      cleanupMeasure inner position innerContents := by
  have population := innerPopulation_update_cons inner innerContents
    stack symbol tail contentsEq
  unfold cleanupMeasure
  omega

theorem cleanupMeasure_next_lt
    (inner : FinTM2)
    (position : Fin (Fintype.card inner.K + 1))
    (innerContents : ∀ stack, List (inner.Γ stack))
    (fits : position.val < Fintype.card inner.K) :
    cleanupMeasure inner (nextCleanupPosition inner position)
        innerContents <
      cleanupMeasure inner position innerContents := by
  rw [cleanupMeasure, cleanupMeasure,
    nextCleanupPosition_val_of_lt inner position fits]
  omega

end TM2EndDelimitedBlockMap
end LeanTrominoes
