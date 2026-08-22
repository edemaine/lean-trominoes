/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListFilteredProductCount

/-! # Mapping both inputs of a filtered Cartesian-product count -/

namespace List

/-- Mapping both input lists can instead be incorporated into the predicate
of a filtered Cartesian-product count. -/
theorem filteredProductCount_map
    (predicate : γ × δ → Bool)
    (firstMap : α → γ) (secondMap : β → δ)
    (firsts : List α) (seconds : List β) :
    filteredProductCount predicate
        (firsts.map firstMap) (seconds.map secondMap) =
      filteredProductCount
        (fun pair => predicate (firstMap pair.1, secondMap pair.2))
        firsts seconds := by
  rw [filteredProductCount_eq_sum_rows,
    filteredProductCount_eq_sum_rows, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro first firstMember
  simp only [Function.comp_apply]
  unfold filteredRowCount
  rw [List.filter_map, List.length_map]
  rfl

end List
