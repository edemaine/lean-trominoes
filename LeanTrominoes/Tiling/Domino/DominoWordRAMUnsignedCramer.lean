/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMCramer

/-! # Lattice tests using only nonnegative remainders and bit-array equality -/
namespace LeanTrominoes.Domino

theorem quotient_parity_natAbs (a b : ℤ) (divisible : b∣a) :
    (a/b)%2=((a.natAbs%(2*b.natAbs)/b.natAbs : ℕ) : ℤ) := by
  have natural : a.natAbs%(2*b.natAbs)/b.natAbs=(a/b).natAbs%2 := by
    rw [Int.natAbs_ediv_of_dvd divisible]
    simpa [Nat.mul_comm] using Nat.mod_mul_right_div_self a.natAbs b.natAbs 2
  rw [natural]
  have parity (q : ℤ) : q%2=((q.natAbs%2 : ℕ) : ℤ) := by
    obtain ⟨n,rfl | rfl⟩ := q.eq_nat_or_neg <;> simp [Int.neg_emod_two,Int.natCast_emod]
  exact parity (a/b)

/-- A residue modulo twice the positive magnitude of the determinant is zero
or exactly that magnitude iff the original signed numerator is divisible. -/
theorem divisible_iff_unsigned_remainder (a b : ℤ) :
    b∣a ↔ a.natAbs%(2*b.natAbs)=0 ∨ a.natAbs%(2*b.natAbs)=b.natAbs := by
  have decomposition := Nat.mod_mul (a := b.natAbs) (b := 2) (x := a.natAbs)
  constructor
  · intro divisible
    have zero := Nat.mod_eq_zero_of_dvd (Int.natAbs_dvd_natAbs.mpr divisible)
    rw [zero,zero_add,Nat.mul_comm b.natAbs 2] at decomposition
    have bit : a.natAbs/b.natAbs%2≤1 := by omega
    have cases : a.natAbs/b.natAbs%2=0 ∨ a.natAbs/b.natAbs%2=1 := by omega
    rcases cases with equal | equal
    · left; rw [decomposition,equal,mul_zero]
    · right; rw [decomposition,equal,mul_one]
  · intro residue
    have reduce := Nat.mod_mul_left_mod a.natAbs 2 b.natAbs
    have zero : a.natAbs%b.natAbs=0 := by
      rcases residue with equal | equal <;> rw [equal] at reduce <;> simpa using reduce.symm
    exact Int.natAbs_dvd_natAbs.mp (Nat.dvd_of_mod_eq_zero zero)

end LeanTrominoes.Domino
