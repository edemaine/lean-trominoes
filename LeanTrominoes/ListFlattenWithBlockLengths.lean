/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import Mathlib.Data.List.Basic

/-! # Recovering block boundaries from a flattened list and block lengths -/

namespace List

/-- A flattened list together with its ordered block lengths determines
every block, including empty blocks. -/
theorem eq_of_flatten_eq_of_map_length_eq {α : Type*}
    {first second : List (List α)}
    (flattenEq : first.flatten = second.flatten)
    (lengthsEq : first.map List.length = second.map List.length) :
    first = second := by
  induction first generalizing second with
  | nil =>
      cases second <;> simp_all
  | cons firstBlock first induction =>
      cases second with
      | nil => simp at lengthsEq
      | cons secondBlock second =>
          have lengths := List.cons.inj lengthsEq
          have headEq := congrArg (List.take firstBlock.length) flattenEq
          have tailEq := congrArg (List.drop firstBlock.length) flattenEq
          simp only [List.flatten_cons] at headEq tailEq
          have blocksEq : firstBlock = secondBlock := by
            rw [List.take_left] at headEq
            simpa only [lengths.1, List.take_left] using headEq
          subst secondBlock
          have restEq : first.flatten = second.flatten := by
            simpa only [List.drop_left] using tailEq
          exact congrArg (List.cons firstBlock) (induction restEq lengths.2)

end List
