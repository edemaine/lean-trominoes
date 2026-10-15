/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.ProdSigma

/-! # Counting filtered Cartesian products by rows -/

namespace List

/-- Number of second-list entries accepted against one fixed first entry. -/
def filteredRowCount (predicate : α × β → Bool)
    (first : α) (seconds : List β) : Nat :=
  (seconds.filter fun second => predicate (first, second)).length

/-- Number of accepted ordered pairs in a Cartesian product. -/
def filteredProductCount (predicate : α × β → Bool)
    (firsts : List α) (seconds : List β) : Nat :=
  ((firsts ×ˢ seconds).filter predicate).length

/-- Filtering the row-major product is the sum of its independently filtered
rows. -/
theorem filteredProductCount_eq_sum_rows
    (predicate : α × β → Bool)
    (firsts : List α) (seconds : List β) :
    filteredProductCount predicate firsts seconds =
      (firsts.map fun first =>
        filteredRowCount predicate first seconds).sum := by
  induction firsts with
  | nil => rfl
  | cons first firsts induction =>
      have rowMap :
          (List.filter predicate
            (seconds.map fun second => (first, second))).length =
            (seconds.filter fun second =>
              predicate (first, second)).length := by
        rw [List.filter_map, List.length_map]
        rfl
      simp only [filteredProductCount, List.product_cons,
        List.filter_append, List.length_append, List.map_cons,
        List.sum_cons, filteredRowCount]
      rw [rowMap]
      change _ + filteredProductCount predicate firsts seconds = _
      rw [induction]
      rfl

/-- A filtered row over flattened blocks is the sum of its block counts. -/
theorem filteredRowCount_flatMap
    (predicate : α × β → Bool) (first : α)
    (blocks : List γ) (values : γ → List β) :
    filteredRowCount predicate first (blocks.flatMap values) =
      (blocks.map fun block =>
        filteredRowCount predicate first (values block)).sum := by
  induction blocks with
  | nil => rfl
  | cons block blocks induction =>
      simp only [filteredRowCount, List.flatMap_cons, List.filter_append,
        List.length_append, List.map_cons, List.sum_cons]
      change _ + filteredRowCount predicate first (blocks.flatMap values) = _
      rw [induction]
      rfl

/-- Flattened first-list blocks can be counted independently without changing
the accepted-pair total. -/
theorem filteredProductCount_flatMap_left
    (predicate : α × β → Bool)
    (blocks : List γ) (values : γ → List α)
    (seconds : List β) :
    filteredProductCount predicate (blocks.flatMap values) seconds =
      (blocks.map fun block =>
        filteredProductCount predicate (values block) seconds).sum := by
  rw [filteredProductCount_eq_sum_rows]
  induction blocks with
  | nil => rfl
  | cons block blocks induction =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons]
      rw [← filteredProductCount_eq_sum_rows]
      rw [induction]

end List
