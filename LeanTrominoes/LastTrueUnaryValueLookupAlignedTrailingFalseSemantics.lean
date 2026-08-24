/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupMachine

/-! # Ignoring an aligned trailing rejected lookup field -/

namespace LeanTrominoes.LastTrueUnaryValueLookupMachine

/-- Appending both a false row bit and its aligned unary value preserves the
incoming last-true lookup result. -/
theorem lookupAux_append_false_append_value_of_length_eq
    (candidate : Nat) (row : List Bool) (values : List Nat) (value : Nat)
    (sameLength : row.length = values.length) :
    lookupAux candidate (row ++ [false]) (values ++ [value]) =
      lookupAux candidate row values := by
  induction row generalizing candidate values with
  | nil =>
      have : values = [] := List.eq_nil_of_length_eq_zero sameLength.symm
      subst values
      rfl
  | cons bit row induction =>
      cases values with
      | nil => simp at sameLength
      | cons head values =>
          simp only [List.length_cons, Nat.succ.injEq] at sameLength
          cases bit <;>
            simpa [lookupAux] using induction _ values sameLength

end LeanTrominoes.LastTrueUnaryValueLookupMachine
