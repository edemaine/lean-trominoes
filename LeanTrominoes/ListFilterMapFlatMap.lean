/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Basic

/-! # Flat mapping after optional list selection -/

namespace List

/-- Expanding an optional value block at every source entry is exactly
expanding the compact `filterMap` result, with the same order. -/
theorem flatMap_toList_flatMap_eq_filterMap_flatMap
    (values : List α) (selected : α → Option β)
    (block : β → List γ) :
    values.flatMap (fun value =>
        (selected value).toList.flatMap block) =
      (values.filterMap selected).flatMap block := by
  rw [List.filterMap_eq_flatMap_toList, List.flatMap_assoc]

end List
