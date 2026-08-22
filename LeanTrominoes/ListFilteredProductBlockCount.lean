/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListFilteredProductCount

/-! # Counting filtered Cartesian products by pairs of blocks -/

namespace List

/-- A filtered product distributes over appending the second input. -/
theorem filteredProductCount_append_right
    (predicate : α × β → Bool)
    (firsts : List α) (firstSeconds secondSeconds : List β) :
    filteredProductCount predicate firsts
        (firstSeconds ++ secondSeconds) =
      filteredProductCount predicate firsts firstSeconds +
        filteredProductCount predicate firsts secondSeconds := by
  unfold filteredProductCount
  induction firsts with
  | nil => rfl
  | cons first firsts induction =>
      simp only [List.product_cons, List.map_append, List.filter_append,
        List.length_append] at induction ⊢
      omega

/-- A flattened second family can be counted one block at a time. -/
theorem filteredProductCount_flatMap_right
    (predicate : α × β → Bool)
    (firsts : List α) (blocks : List γ)
    (values : γ → List β) :
    filteredProductCount predicate firsts (blocks.flatMap values) =
      (blocks.map fun block =>
        filteredProductCount predicate firsts (values block)).sum := by
  induction blocks with
  | nil => simp [filteredProductCount]
  | cons block blocks induction =>
      rw [List.flatMap_cons, filteredProductCount_append_right,
        induction]
      rfl

/-- Filtering two flattened block families is the sum of the independently
filtered ordered block-pair products. -/
theorem filteredProductCount_flatMap_blocks
    (predicate : α × β → Bool)
    (firstBlocks : List γ) (firstValues : γ → List α)
    (secondBlocks : List δ) (secondValues : δ → List β) :
    filteredProductCount predicate
        (firstBlocks.flatMap firstValues)
        (secondBlocks.flatMap secondValues) =
      ((firstBlocks ×ˢ secondBlocks).map fun pair =>
        filteredProductCount predicate
          (firstValues pair.1) (secondValues pair.2)).sum := by
  rw [filteredProductCount_flatMap_left]
  induction firstBlocks with
  | nil => rfl
  | cons first firstBlocks induction =>
      simp only [List.map_cons, List.sum_cons, List.product_cons,
        List.map_append, List.sum_append, List.map_map,
        Function.comp_def]
      rw [filteredProductCount_flatMap_right, induction]

end List
