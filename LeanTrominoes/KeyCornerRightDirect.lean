/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyCornerCandidates
import Mathlib.Tactic.IntervalCases

/-! # Kernel-checked right corner certificates (direct) -/

namespace LeanTrominoes.KeyCornerArithmetic.Certificates

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem right_identity :
    ∀ x y : Fin 104,
      compatible 96 .identity ((x.val : Int) - 4, (y.val : Int) - 4) rightOffsets →
        SquareSymmetry.identity = .identity ∧ ((x.val : Int) - 4, (y.val : Int) - 4) = (-4, 2) := by
  intro x
  have hx := x.isLt
  interval_cases x.val
  all_goals decide +kernel

theorem right_rotate90 :
    ∀ x y : Fin 104,
      compatible 96 .rotate90 ((x.val : Int) - 4, (y.val : Int) - 4) rightOffsets →
        SquareSymmetry.rotate90 = .identity ∧ ((x.val : Int) - 4, (y.val : Int) - 4) = (-4, 2) := by
  intro x
  have hx := x.isLt
  interval_cases x.val
  all_goals decide +kernel

theorem right_rotate180 :
    ∀ x y : Fin 104,
      compatible 96 .rotate180 ((x.val : Int) - 4, (y.val : Int) - 4) rightOffsets →
        SquareSymmetry.rotate180 = .identity ∧ ((x.val : Int) - 4, (y.val : Int) - 4) = (-4, 2) := by
  intro x
  have hx := x.isLt
  interval_cases x.val
  all_goals decide +kernel

theorem right_rotate270 :
    ∀ x y : Fin 104,
      compatible 96 .rotate270 ((x.val : Int) - 4, (y.val : Int) - 4) rightOffsets →
        SquareSymmetry.rotate270 = .identity ∧ ((x.val : Int) - 4, (y.val : Int) - 4) = (-4, 2) := by
  intro x
  have hx := x.isLt
  interval_cases x.val
  all_goals decide +kernel

end LeanTrominoes.KeyCornerArithmetic.Certificates
