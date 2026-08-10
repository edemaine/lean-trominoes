import LeanTrominoes.PeriodicThreeDMNormalizationCellTypeComputability

/-!
# Primitive-recursive normalized torus locations

This module implements integer remainder by a natural modulus on Mathlib's
integer encoding, then applies the north/south reflection used by the final
finite-torus rasterization.
-/

noncomputable section

namespace LeanTrominoes

open Gadget
open LeanTrominoes.Computability

namespace PeriodicThreeDM
namespace NormalizationCompiler

set_option maxHeartbeats 400000
set_option maxRecDepth 10000

def intEmodNat (integer : Int) (modulus : Nat) : Int :=
  if modulus = 0 then integer
  else
    let remainder := integer.natAbs % modulus
    if 0 ≤ integer then
      Int.ofNat remainder
    else if remainder = 0 then
      0
    else
      Int.ofNat (modulus - remainder)

theorem intEmodNat_eq (integer : Int) (modulus : Nat) :
    intEmodNat integer modulus = integer % (modulus : Int) := by
  by_cases modulusZero : modulus = 0
  · simp [intEmodNat, modulusZero]
  rw [intEmodNat, if_neg modulusZero]
  by_cases nonnegative : 0 ≤ integer
  · rw [if_pos nonnegative, ← Int.natAbs_of_nonneg nonnegative,
      ← Int.natCast_emod]
    simp only [Int.natAbs_natCast, Int.ofNat_eq_natCast]
  · rw [if_neg nonnegative]
    have negative : integer < 0 := lt_of_not_ge nonnegative
    have magnitude : (integer.natAbs : Int) = -integer := by
      simpa using Int.natAbs_of_nonneg (show 0 ≤ -integer by omega)
    have integerEq : integer = -(integer.natAbs : Int) := by omega
    rw [integerEq, Int.neg_emod]
    simp only [Int.natAbs_neg, Int.natAbs_natCast,
      Int.ofNat_eq_natCast, Int.natCast_dvd_natCast]
    rw [← Int.natCast_emod]
    by_cases divides : modulus ∣ integer.natAbs
    · simp [divides, Nat.mod_eq_zero_of_dvd divides]
    · have remainderNe : integer.natAbs % modulus ≠ 0 := by
        exact fun remainderZero =>
          divides ((Nat.dvd_iff_mod_eq_zero).2 remainderZero)
      rw [if_neg remainderNe, if_neg divides]
      rw [Nat.cast_sub (Nat.le_of_lt
        (Nat.mod_lt _ (Nat.pos_of_ne_zero modulusZero)))]

theorem intEmodNat_primrec :
    Primrec₂ intEmodNat := by
  change Primrec fun input : Int × Nat =>
    intEmodNat input.1 input.2
  have magnitude : Primrec (fun input : Int × Nat =>
      input.1.natAbs) :=
    int_natAbs_primrec.comp Primrec.fst
  have remainder : Primrec (fun input : Int × Nat =>
      input.1.natAbs % input.2) :=
    Primrec.nat_mod.comp magnitude Primrec.snd
  have modulusZero : PrimrecPred fun input : Int × Nat =>
      input.2 = 0 :=
    Primrec.eq.comp Primrec.snd (Primrec.const 0)
  have nonnegative : PrimrecPred fun input : Int × Nat =>
      0 ≤ input.1 :=
    int_nonnegative_primrec.comp Primrec.fst
  have remainderZero : PrimrecPred fun input : Int × Nat =>
      input.1.natAbs % input.2 = 0 :=
    Primrec.eq.comp remainder (Primrec.const 0)
  have positiveResult : Primrec (fun input : Int × Nat =>
      Int.ofNat (input.1.natAbs % input.2)) :=
    int_ofNat_primrec.comp remainder
  have negativeResult : Primrec (fun input : Int × Nat =>
      Int.ofNat (input.2 - input.1.natAbs % input.2)) :=
    int_ofNat_primrec.comp
      (Primrec.nat_sub.comp Primrec.snd remainder)
  exact (Primrec.ite modulusZero Primrec.fst
    (Primrec.ite nonnegative positiveResult
      (Primrec.ite remainderZero (Primrec.const 0)
        negativeResult))).of_eq fun _ => rfl

theorem rasterLocation_primrec :
    Primrec fun input : Nat × Cell =>
      rasterLocation input.1 input.2 := by
  have horizontal : Primrec (fun input : Nat × Cell =>
      input.2.1 % (input.1 : Int)) :=
    (intEmodNat_primrec.comp
      (Primrec.fst.comp Primrec.snd) Primrec.fst).of_eq
        fun input => intEmodNat_eq input.2.1 input.1
  have vertical : Primrec (fun input : Nat × Cell =>
      (-input.2.2) % (input.1 : Int)) :=
    (intEmodNat_primrec.comp
      (int_negate_primrec.comp (Primrec.snd.comp Primrec.snd))
      Primrec.fst).of_eq
        fun input => intEmodNat_eq (-input.2.2) input.1
  exact (Primrec.pair horizontal vertical).of_eq fun _ => rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
