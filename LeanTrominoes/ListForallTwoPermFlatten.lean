/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Perm.Basic

/-! # Flattening pointwise list permutations -/

namespace List.Forall₂

/-- Flattening two lists of lists related pointwise by permutation preserves
the combined multiset. -/
theorem flatten_perm {Element : Type*}
    {first second : List (List Element)}
    (related : List.Forall₂ List.Perm first second) :
    first.flatten.Perm second.flatten := by
  induction related with
  | nil => exact List.Perm.nil
  | cons head _ induction =>
      simp only [List.flatten_cons]
      exact head.append induction

end List.Forall₂
