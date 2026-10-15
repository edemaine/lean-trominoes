/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.ProdSigma

/-! # Flattening nested loops over a list product -/

namespace LeanTrominoes

/-- Nested loops and product order give the same flattened pair blocks. -/
theorem nested_flatMap_eq_product_flatMap
    {First Second Output : Type}
    (firsts : List First) (seconds : List Second)
    (blocks : First × Second → List Output) :
    firsts.flatMap (fun first =>
        seconds.flatMap fun second => blocks (first, second)) =
      (firsts ×ˢ seconds).flatMap blocks := by
  induction firsts with
  | nil => rfl
  | cons first firsts induction =>
      simp [List.flatMap_map, induction]

end LeanTrominoes
