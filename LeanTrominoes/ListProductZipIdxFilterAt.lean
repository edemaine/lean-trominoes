/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListProductFilterAnd
import LeanTrominoes.ListZipIdxFilterAt

/-! # Filtering an indexed list product at one position pair -/

namespace List

/-- Filtering a row-major indexed product at two indices returns their
unique pair when both entries are present, and nothing otherwise. -/
theorem filter_product_zipIdx_eq_indices
    (firsts : List α) (seconds : List β)
    (firstIndex secondIndex : Nat) :
    (firsts.zipIdx ×ˢ seconds.zipIdx).filter (fun pair =>
      decide (firstIndex = pair.1.2) &&
        decide (secondIndex = pair.2.2)) =
      match firsts[firstIndex]?, seconds[secondIndex]? with
      | some first, some second =>
          [((first, firstIndex), (second, secondIndex))]
      | _, _ => [] := by
  rw [List.filter_product_and
      firsts.zipIdx seconds.zipIdx
      (fun tagged => decide (firstIndex = tagged.2))
      (fun tagged => decide (secondIndex = tagged.2)),
    List.filter_zipIdx_eq_index,
    List.filter_zipIdx_eq_index]
  cases firsts[firstIndex]? <;> cases seconds[secondIndex]? <;> rfl

end List
