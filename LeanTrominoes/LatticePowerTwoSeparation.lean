/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic

/-! # A polynomial-size power-of-two cover separates elements of order two -/
namespace LeanTrominoes.ImplicationGraph

/-- The next strictly larger power of two, bounded by twice the input plus two. -/
def coverPeriod (bound : Nat) : Nat := 2^(Nat.log 2 bound+1)

theorem coverPeriod_gt (bound : Nat) : bound < coverPeriod bound :=
  Nat.lt_pow_succ_log_self (by decide) bound

theorem coverPeriod_le (bound : Nat) : coverPeriod bound ≤ 2*(bound+1) := by
  unfold coverPeriod
  rw [pow_succ]
  have := Nat.pow_log_le_add_one 2 bound
  omega

theorem gcd_double_power_dvd (delta : Int) (nonzero : delta ≠ 0) (k : Nat)
    (small : delta.natAbs < 2^k) : delta.gcd (2*(2^k : Nat)) ∣ 2^k := by
  have dvd : delta.gcd (2*(2^k : Nat)) ∣ 2^(k+1) := by
    have one := (Int.natCast_dvd_natCast).mp (Int.gcd_dvd_right delta ((2*(2^k : Nat) : Nat) : Int))
    simpa [pow_succ,Nat.mul_comm] using one
  by_contra absent
  have equal := Nat.eq_prime_pow_of_dvd_least_prime_pow Nat.prime_two absent dvd
  have left : delta.gcd (2*(2^k : Nat)) ∣ delta.natAbs := Int.gcd_dvd_natAbs_left _ _
  have le := Nat.le_of_dvd (Int.natAbs_pos.mpr nonzero) left
  rw [equal] at le
  have grow : 2^k ≤ 2^(k+1) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

variable {G : Type*} [AddCommGroup G]

private theorem gcd_smul_mem (H : AddSubgroup G) (z : G) (a b : Int)
    (ha : a • z ∈ H) (hb : b • z ∈ H) : (a.gcd b : Int) • z ∈ H := by
  rw [Int.gcd_eq_gcd_ab,add_zsmul,mul_zsmul,mul_zsmul]
  rw [smul_comm a,smul_comm b]
  exact H.add_mem (H.zsmul_mem ha _) (H.zsmul_mem hb _)

/-- A bounded nonzero saturation multiplier rules out false contradictions in the cover.
The multiplier need not be computed by the algorithm. -/
theorem order_two_separated (H : AddSubgroup G) (delta : Int) (nonzero : delta ≠ 0)
    (saturation : ∀ (z : G) (c : Int), c ≠ 0 → c • z ∈ H → delta • z ∈ H)
    (k : Nat) (small : delta.natAbs < 2^k) (a h z : G) (hh : h ∈ H)
    (twice : a+a ∈ H) (equal : a=h+(2^k : Nat) • z) : a ∈ H := by
  have double : ((2*(2^k : Nat) : Nat) : Int) • z ∈ H := by
    have member := H.sub_mem twice (H.add_mem hh hh)
    convert member using 1
    rw [equal]
    simp only [natCast_zsmul,mul_smul,two_smul]
    abel
  have nonzeroDouble : ((2*(2^k : Nat) : Nat) : Int) ≠ 0 := by positivity
  have saturated := saturation z _ nonzeroDouble double
  have gcdMember := gcd_smul_mem H z delta ((2*(2^k : Nat) : Nat) : Int) saturated double
  obtain ⟨q,hq⟩ := gcd_double_power_dvd delta nonzero k small
  have scaled := H.zsmul_mem gcdMember (q : Int)
  have periodMember : (2^k : Nat) • z ∈ H := by
    rw [← natCast_zsmul, hq, Nat.cast_mul,mul_smul,smul_comm]
    exact scaled
  rw [equal]
  exact H.add_mem hh periodMember

end LeanTrominoes.ImplicationGraph
