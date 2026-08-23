/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Basic

/-! # Euclidean quotients after integral period shifts -/

namespace LeanTrominoes

/-- Adding an integral period shift to a coordinate in the canonical period
changes its Euclidean quotient by exactly that shift. -/
theorem coordinate_add_period_mul_ediv_eq_shift
    {period : Nat} (periodPositive : 0 < period)
    {coordinate : Int}
    (coordinateNonnegative : 0 ≤ coordinate)
    (coordinateSmall : coordinate < period)
    (shift : Int) :
    (coordinate + period * shift) / period = shift := by
  have periodNe : (period : Int) ≠ 0 :=
    Int.ofNat_ne_zero.mpr (Nat.ne_of_gt periodPositive)
  have coordinateQuotient : coordinate / (period : Int) = 0 := by
    exact Int.ediv_eq_zero_of_lt coordinateNonnegative coordinateSmall
  rw [Int.mul_comm (period : Int) shift,
    Int.add_mul_ediv_right _ _ periodNe,
    coordinateQuotient, Int.zero_add]

end LeanTrominoes
