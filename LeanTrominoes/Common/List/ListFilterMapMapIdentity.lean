/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Basic

/-! # Filtering a mapped list by the identity option map -/

namespace List

/-- If mapping an option-valued function gives a target list, filtering that
function is the same as filtering the target by `id`. -/
theorem filterMap_eq_filterMap_id_of_map_eq
    (source : List α) (function : α → Option β) (target : List (Option β))
    (mapped : source.map function = target) :
    source.filterMap function = target.filterMap id := by
  rw [← mapped, List.filterMap_map]
  rfl

end List
