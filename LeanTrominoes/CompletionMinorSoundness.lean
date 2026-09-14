/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionMinorCertificates

/-! # Exact equal/not relations for the finite completion gadgets -/

namespace LeanTrominoes.CompletionMinor

/-- The actual prefill has precisely the intended equal/not relation when
one cell of each connector pair is assigned to the neighboring brick. -/
theorem completable_iff_output (t : Tromino) (gate : Gate) (a b : Bool) :
    t.Completable (target t gate a b : Set Cell)
      (t.finiteFootprints (prefill t gate) : Set (Finset Cell)) ↔ b = output gate a := by
  constructor
  · intro h
    by_contra wrong
    have eq : b = !(output gate a) := by cases hval : output gate a <;> cases b <;> simp_all
    subst b
    exact TrominoFiniteCover.not_tileable_of_search_empty _ _ (wrong_state_search_empty t gate a)
      (residual_tileable_of_completable t gate a _ h)
  · rintro rfl
    exact intended_state_completable t gate a

end LeanTrominoes.CompletionMinor
