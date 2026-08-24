/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Basic

/-! # Singleton-block form of list filtering -/

namespace LeanTrominoes

/-- Flattening singleton-or-empty blocks is exactly filtering and mapping. -/
theorem flatMap_singleton_if_eq_filter_map
    {Input Output : Type}
    (values : List Input) (predicate : Input → Bool)
    (output : Input → Output) :
    values.flatMap (fun value =>
        if predicate value then [output value] else []) =
      (values.filter predicate).map output := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      cases accepted : predicate value <;>
        simp [accepted, induction]

end LeanTrominoes
