/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionBooleanStates
import LeanTrominoes.CompletionIGuardedEqBoundary
import LeanTrominoes.CompletionIGuardedNegBoundary
import LeanTrominoes.CompletionIGuardedPlugTopBoundary
import LeanTrominoes.CompletionIGuardedPlugBotBoundary
import LeanTrominoes.CompletionIGuardedDup
import LeanTrominoes.CompletionIGuardedTftsat

/-! # Exact boundary relations of the guarded I gadgets -/

namespace LeanTrominoes.CompletionPattern

theorem i_guarded_eq_boundary (i : Fin 16) :
    IGuardedEqBoundary.pattern.Completable (IGuardedEqBoundary.outside i) ↔ i = 3 ∨ i = 6 ∨ i = 9 ∨ i = 12 := by
  rw [IGuardedEqBoundary.completable_iff]
  revert i
  decide +kernel

theorem i_guarded_neg_boundary (i : Fin 16) :
    IGuardedNegBoundary.pattern.Completable (IGuardedNegBoundary.outside i) ↔ i = 5 ∨ i = 10 := by
  rw [IGuardedNegBoundary.completable_iff]
  revert i
  decide +kernel

theorem i_guarded_plugtop_boundary (i : Fin 16) :
    IGuardedPlugTopBoundary.pattern.Completable (IGuardedPlugTopBoundary.outside i) ↔ i = 9 ∨ i = 10 := by
  rw [IGuardedPlugTopBoundary.completable_iff]
  revert i
  decide +kernel

theorem i_guarded_plugbot_boundary (i : Fin 16) :
    IGuardedPlugBotBoundary.pattern.Completable (IGuardedPlugBotBoundary.outside i) ↔ i = 5 ∨ i = 9 := by
  rw [IGuardedPlugBotBoundary.completable_iff]
  revert i
  decide +kernel

theorem i_guarded_duplicator (a b c d : Bool) :
    IGuardedDup.pattern.Completable (IGuardedDup.outside (state4 a b c d)) ↔ a = b ∧ b = c ∧ c = d := by
  rw [IGuardedDup.completable_iff]
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

theorem i_guarded_clause (a b c d : Bool) :
    IGuardedTftsat.pattern.Completable (IGuardedTftsat.outside (state4 a b c d)) ↔
      d = false ∧ (a = true ∨ b = false ∨ c = true) := by
  rw [IGuardedTftsat.completable_iff]
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

end LeanTrominoes.CompletionPattern
