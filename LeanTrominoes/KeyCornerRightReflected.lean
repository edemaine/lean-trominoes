/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyCornerCandidates
import Mathlib.Tactic.IntervalCases

/-! # Kernel-checked right corner certificates (reflected) -/

namespace LeanTrominoes.KeyCornerArithmetic.Certificates

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem right_reflectX :
    ∀ x y : Fin 104,
      compatible 96 .reflectX ((x.val : Int) - 4, (y.val : Int) - 4) rightOffsets →
        SquareSymmetry.reflectX = .identity ∧ ((x.val : Int) - 4, (y.val : Int) - 4) = (-4, 2) := by
  intro x
  have hx := x.isLt
  interval_cases x.val
  all_goals decide +kernel

theorem right_reflectDiagonal :
    ∀ x y : Fin 104,
      compatible 96 .reflectDiagonal ((x.val : Int) - 4, (y.val : Int) - 4) rightOffsets →
        SquareSymmetry.reflectDiagonal = .identity ∧ ((x.val : Int) - 4, (y.val : Int) - 4) = (-4, 2) := by
  intro x
  have hx := x.isLt
  interval_cases x.val
  all_goals decide +kernel

theorem right_reflectY :
    ∀ x y : Fin 104,
      compatible 96 .reflectY ((x.val : Int) - 4, (y.val : Int) - 4) rightOffsets →
        SquareSymmetry.reflectY = .identity ∧ ((x.val : Int) - 4, (y.val : Int) - 4) = (-4, 2) := by
  intro x
  have hx := x.isLt
  interval_cases x.val
  all_goals decide +kernel

theorem right_reflectAntidiagonal :
    ∀ x y : Fin 104,
      compatible 96 .reflectAntidiagonal ((x.val : Int) - 4, (y.val : Int) - 4) rightOffsets →
        SquareSymmetry.reflectAntidiagonal = .identity ∧ ((x.val : Int) - 4, (y.val : Int) - 4) = (-4, 2) := by
  intro x
  have hx := x.isLt
  interval_cases x.val
  all_goals decide +kernel

end LeanTrominoes.KeyCornerArithmetic.Certificates
