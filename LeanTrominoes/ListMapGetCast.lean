/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Basic

/-! # Indexed lookup through an exact list map -/

namespace List

/-- An exact map equality transports lookup at a shared fixed length. -/
theorem map_get_cast_eq
    (values : List α) (target : List β) (function : α → β)
    (count : Nat)
    (valuesLength : values.length = count)
    (targetLength : target.length = count)
    (mapped : values.map function = target)
    (index : Fin count) :
    function (values.get (Fin.cast valuesLength.symm index)) =
      target.get (Fin.cast targetLength.symm index) := by
  subst target
  simp

end List
