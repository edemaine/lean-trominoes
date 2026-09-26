/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.NativeScalarAdapters

namespace LeanTrominoes.NativeScalar
open BoundedArithmetic BoundedArithmetic.Expr

def conjunction (left right : Program) : Program :=
  combine left right (andE (var 1) (var 0)) (by decide)

theorem conjunction_truth (left right : Program) (values : List Nat) :
    (conjunction left right).value values ≠ 0 ↔ left.value values ≠ 0 ∧ right.value values ≠ 0 := by
  change (andE (var 1) (var 0)).Truth (right.value values::left.value values::values) ↔ _
  rw [truth_and]
  rfl

end LeanTrominoes.NativeScalar
