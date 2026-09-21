/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BoundedArithmeticCount
import Mathlib.Data.Finset.Card

/-! # Counting marked addresses below a runtime bound -/
namespace LeanTrominoes.BoundedArithmetic.Count
open Expr

theorem count_addresses (body : Expr) (values : List Nat) (bound : Nat) (addresses : List Nat)
    (distinct : addresses.Nodup)
    (members : ∀ p, p ∈ addresses ↔ body.Truth (p::values)) :
    count body values bound = (addresses.filter fun p => decide (p<bound)).length := by
  rw [count_eq_length_filter]
  have equal : ((List.range bound).filter (fun p => decide (body.eval (p::values) ≠ 0))).toFinset =
      (addresses.filter fun p => decide (p<bound)).toFinset := by
    ext p
    simp only [List.mem_toFinset,List.mem_filter,List.mem_range,decide_eq_true_eq,members,Truth]
    exact and_comm
  rw [← List.toFinset_card_of_nodup ((List.nodup_range (n := bound)).filter _),equal,
    List.toFinset_card_of_nodup (distinct.filter _)]

end LeanTrominoes.BoundedArithmetic.Count
