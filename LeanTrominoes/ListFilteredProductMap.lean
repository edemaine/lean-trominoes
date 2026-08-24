/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.ProdSigma

/-! # Mapping both inputs of a filtered Cartesian product -/

namespace List

/-- Mapping both inputs of a filtered Cartesian product can instead be
incorporated into its predicate and final pair map, preserving exact order. -/
theorem filteredProduct_map
    (predicate : γ × δ → Bool)
    (firstMap : α → γ) (secondMap : β → δ)
    (firsts : List α) (seconds : List β) :
    ((firsts.map firstMap) ×ˢ
        (seconds.map secondMap)).filter predicate =
      ((firsts ×ˢ seconds).filter fun pair =>
        predicate (firstMap pair.1, secondMap pair.2)).map fun pair =>
          (firstMap pair.1, secondMap pair.2) := by
  induction firsts with
  | nil => rfl
  | cons first firsts induction =>
      have rowEq :
          ((seconds.map secondMap).map fun second =>
              (firstMap first, second)).filter predicate =
            ((seconds.map fun second => (first, second)).filter fun pair =>
              predicate (firstMap pair.1, secondMap pair.2)).map fun pair =>
                (firstMap pair.1, secondMap pair.2) := by
        rw [List.map_map, List.filter_map, List.filter_map,
          List.map_map]
        rfl
      simp only [List.map_cons, List.product_cons, List.filter_append,
        List.map_append, induction]
      rw [rowEq]

end List
