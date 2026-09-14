/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionBooleanStates
import LeanTrominoes.CompletionIDup
import LeanTrominoes.CompletionLDup
import LeanTrominoes.CompletionITftsat
import LeanTrominoes.CompletionL3Sat

/-! # Boolean relations of the major completion subbricks

Each boundary pair assigns one cell to the neighboring brick. The bit order
is top left, top right, bottom left, bottom right.
-/

namespace LeanTrominoes.CompletionPattern

theorem i_duplicator (a b c d : Bool) :
    IDup.pattern.Completable (IDup.outside (state4 a b c d)) ↔ a = b ∧ b = c ∧ c = d := by
  rw [IDup.completable_iff]
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

theorem l_duplicator (a b c d : Bool) :
    LDup.pattern.Completable (LDup.outside (state4 a b c d)) ↔ a = b ∧ b = c ∧ c = d := by
  rw [LDup.completable_iff]
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

theorem i_clause (a b c d : Bool) :
    ITftsat.pattern.Completable (ITftsat.outside (state4 a b c d)) ↔
      d = false ∧ (a = true ∨ b = false ∨ c = true) := by
  rw [ITftsat.completable_iff]
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

theorem l_clause (a b c d : Bool) :
    L3Sat.pattern.Completable (L3Sat.outside (state4 a b c d)) ↔
      d = false ∧ (a = true ∨ b = true ∨ c = true) := by
  rw [L3Sat.completable_iff]
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

end LeanTrominoes.CompletionPattern
