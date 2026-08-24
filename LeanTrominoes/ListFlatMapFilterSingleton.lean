/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Basic

/-! # Conditional singleton flat maps as filtered maps -/

namespace LeanTrominoes

/-- Emitting one output exactly on a keyed predicate equals filtering first
and then mapping the output. -/
theorem flatMap_if_singleton_eq_filter_map
    {Value Key Output : Type*} [DecidableEq Key]
    (values : List Value) (key : Value → Key) (selected : Key)
    (output : Value → Output) :
    (values.flatMap fun value =>
        if key value = selected then [output value] else []) =
      (values.filter fun value => key value = selected).map output := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      by_cases keyEq : key value = selected
      · simp [keyEq, induction]
      · simp [keyEq, induction]

end LeanTrominoes
