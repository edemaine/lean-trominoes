/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2EndDelimitedBlockMapCleanupSteps

/-! # Finite stack indices used by block-map cleanup -/

noncomputable section

namespace LeanTrominoes
namespace TM2EndDelimitedBlockMap

open Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

def cleanupIndex (inner : FinTM2) (stack : inner.K) : Nat :=
  (Fintype.equivFin inner.K stack).val

def ClearedBefore (inner : FinTM2)
    (position : Fin (Fintype.card inner.K + 1))
    (innerContents : ∀ stack, List (inner.Γ stack)) : Prop :=
  ∀ stack, cleanupIndex inner stack < position.val →
    innerContents stack = []

theorem cleanupStack_some_lt (inner : FinTM2)
    (position : Fin (Fintype.card inner.K + 1)) (stack : inner.K)
    (selected : cleanupStack inner position = some stack) :
    position.val < Fintype.card inner.K := by
  unfold cleanupStack at selected
  split at selected <;> simp_all

theorem cleanupStack_some_index (inner : FinTM2)
    (position : Fin (Fintype.card inner.K + 1)) (stack : inner.K)
    (selected : cleanupStack inner position = some stack) :
    cleanupIndex inner stack = position.val := by
  unfold cleanupStack at selected
  split at selected
  · simp only [Option.some.injEq] at selected
    subst stack
    simp [cleanupIndex]
  · simp at selected

theorem nextCleanupPosition_val_of_lt (inner : FinTM2)
    (position : Fin (Fintype.card inner.K + 1))
    (fits : position.val < Fintype.card inner.K) :
    (nextCleanupPosition inner position).val = position.val + 1 := by
  change min (position.val + 1) (Fintype.card inner.K) =
    position.val + 1
  exact Nat.min_eq_left (Nat.succ_le_iff.mpr fits)

theorem clearedBefore_zero (inner : FinTM2)
    (innerContents : ∀ stack, List (inner.Γ stack)) :
    ClearedBefore inner ⟨0, by omega⟩ innerContents := by
  intro stack before
  change cleanupIndex inner stack < 0 at before
  exact (Nat.not_lt_zero _ before).elim

theorem ClearedBefore.update_current
    (inner : FinTM2)
    (position : Fin (Fintype.card inner.K + 1))
    (stack : inner.K)
    (innerContents : ∀ target, List (inner.Γ target))
    (value : List (inner.Γ stack))
    (cleared : ClearedBefore inner position innerContents)
    (selected : cleanupStack inner position = some stack) :
    ClearedBefore inner position
      (Function.update innerContents stack value) := by
  intro target before
  have targetNe : target ≠ stack := by
    intro equal
    subst target
    rw [cleanupStack_some_index inner position stack selected] at before
    omega
  rw [Function.update_of_ne targetNe]
  exact cleared target before

theorem ClearedBefore.next
    (inner : FinTM2)
    (position : Fin (Fintype.card inner.K + 1))
    (stack : inner.K)
    (innerContents : ∀ target, List (inner.Γ target))
    (cleared : ClearedBefore inner position innerContents)
    (selected : cleanupStack inner position = some stack)
    (contentsEq : innerContents stack = []) :
    ClearedBefore inner (nextCleanupPosition inner position)
      innerContents := by
  have fits := cleanupStack_some_lt inner position stack selected
  have selectedIndex := cleanupStack_some_index inner position stack selected
  have nextVal := nextCleanupPosition_val_of_lt inner position fits
  intro target beforeNext
  by_cases before : cleanupIndex inner target < position.val
  · exact cleared target before
  · have equalIndex : cleanupIndex inner target = position.val := by
      omega
    have targetEq : target = stack := by
      apply (Fintype.equivFin inner.K).injective
      apply Fin.ext
      exact equalIndex.trans selectedIndex.symm
    subst target
    exact contentsEq

theorem cleanupStack_none_position (inner : FinTM2)
    (position : Fin (Fintype.card inner.K + 1))
    (finished : cleanupStack inner position = none) :
    position.val = Fintype.card inner.K := by
  unfold cleanupStack at finished
  split at finished
  · simp at finished
  · omega

theorem innerContents_eq_empty_of_clearedBefore_finished
    (inner : FinTM2)
    (position : Fin (Fintype.card inner.K + 1))
    (innerContents : ∀ stack, List (inner.Γ stack))
    (cleared : ClearedBefore inner position innerContents)
    (finished : cleanupStack inner position = none) :
    innerContents = emptyInnerStacks inner := by
  funext stack
  change innerContents stack = []
  apply cleared stack
  rw [cleanupStack_none_position inner position finished]
  exact (Fintype.equivFin inner.K stack).isLt

end TM2EndDelimitedBlockMap
end LeanTrominoes
