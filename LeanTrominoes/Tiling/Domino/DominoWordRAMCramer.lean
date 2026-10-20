/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.PeriodicDominoBasis
import Mathlib.Data.Int.NatAbs

/-! # Divisibility and parity tests for integer lattice decoding

The decoder only needs the parities of lattice coordinates. Divisibility of
adjugate numerators tests membership, and their remainders modulo twice the
absolute determinant give these parities without reconstructing coordinates.
-/
namespace LeanTrominoes.Domino
variable {d : ℕ}

/-- Cramer's divisibility test, with no coordinate reconstruction test. -/
theorem lattice_mem_iff_adjugate_dvd
    (A : Matrix (Fin d) (Fin d) ℤ) (nonzero : A.det ≠ 0) (x : Fin d → ℤ) :
    (∃ z, A.mulVec z = x) ↔ ∀ i, A.det ∣ A.adjugate.mulVec x i := by
  constructor
  · rintro ⟨z, rfl⟩ i
    simp only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
      Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul]
    exact dvd_mul_right _ _
  · intro divisible
    let z : Fin d → ℤ := fun i => A.adjugate.mulVec x i / A.det
    have coordinates : (fun i => A.det * z i) = A.adjugate.mulVec x := by
      funext i
      exact (mul_comm _ _).trans (Int.ediv_mul_cancel (divisible i))
    have scaled : (fun i => A.det * A.mulVec z i) = fun i => A.det * x i := by
      calc
        (fun i => A.det * A.mulVec z i) = A.mulVec (fun i => A.det * z i) := by
          funext i
          simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = A.mulVec (A.adjugate.mulVec x) := congrArg A.mulVec coordinates
        _ = fun i => A.det * x i := by
          funext i
          simp only [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
            Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul]
    exact ⟨z, funext fun i => mul_left_cancel₀ nonzero (congrFun scaled i)⟩

/-- Multiples of a positive denominator retain precisely one parity bit. -/
theorem mul_emod_twice (t z : ℤ) (positive : 0 < t) :
    (t * z) % (2 * t) = t * (z % 2) := by
  have decomposition : t * z = t * (z % 2) + (z / 2) * (2 * t) := by
    linear_combination t * (Int.emod_add_mul_ediv z 2).symm
  rw [decomposition, Int.add_mul_emod_self_right]
  apply Int.emod_eq_of_lt
  · exact mul_nonneg (le_of_lt positive) (Int.emod_nonneg z (by decide))
  · nlinarith [Int.emod_lt_of_pos z (by decide : (0 : ℤ) < 2)]

/-- The quotient parity is obtained from a single remainder; divisor sign
has no effect on parity. -/
theorem quotient_parity_of_dvd (a b : ℤ) (nonzero : b ≠ 0) (divisible : b ∣ a) :
    (a / b) % 2 = (a % (2 * |b|)) / |b| := by
  obtain ⟨z, rfl⟩ := divisible
  rw [Int.mul_ediv_cancel_left z nonzero]
  have positive : 0 < |b| := abs_pos.mpr nonzero
  rcases (abs_eq (le_of_lt positive)).mp rfl with equal | equal
  · rw [equal, abs_abs, mul_emod_twice _ _ positive, Int.mul_ediv_cancel_left _ (ne_of_gt positive)]
  · rw [equal, abs_neg, abs_abs]
    have product : -|b| * z = |b| * -z := by ring
    rw [product, mul_emod_twice _ _ positive,
      Int.mul_ediv_cancel_left _ (ne_of_gt positive), Int.neg_emod_two]

/-- Complete decoder criterion, including all coordinate parity bits. -/
theorem lattice_coordinates_parity
    (A : Matrix (Fin d) (Fin d) ℤ) (nonzero : A.det ≠ 0)
    (x z : Fin d → ℤ) (realizes : A.mulVec z = x) (i : Fin d) :
    z i % 2 = (A.adjugate.mulVec x i % (2 * |A.det|)) / |A.det| := by
  have numerator : A.adjugate.mulVec x i = A.det * z i := by
    rw [← realizes]
    simp only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
      Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul]
  have divisible : A.det ∣ A.adjugate.mulVec x i := by rw [numerator]; exact dvd_mul_right _ _
  have quotient := quotient_parity_of_dvd (A.adjugate.mulVec x i) A.det nonzero divisible
  simpa only [numerator, Int.mul_ediv_cancel_left _ nonzero] using quotient

end LeanTrominoes.Domino
