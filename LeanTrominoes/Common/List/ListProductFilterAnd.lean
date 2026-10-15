/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.ProdSigma

/-! # Filtering both coordinates of a list product -/

namespace List

/-- Filtering a row-major product by independent Boolean coordinate tests is
the row-major product of the two filtered lists. -/
theorem filter_product_and
    (firsts : List α) (seconds : List β)
    (firstSelected : α → Bool) (secondSelected : β → Bool) :
    (firsts ×ˢ seconds).filter (fun pair =>
      firstSelected pair.1 && secondSelected pair.2) =
      firsts.filter firstSelected ×ˢ seconds.filter secondSelected := by
  induction firsts with
  | nil => rfl
  | cons first firsts induction =>
      rw [List.product_cons, List.filter_append, List.filter_map,
        induction]
      cases selected : firstSelected first <;>
        simp [selected, List.product_cons, Function.comp_def]

end List
