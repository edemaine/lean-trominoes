/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMAbsolute

/-! # Connecting binary arrays to signed mathematical integers -/
namespace LeanTrominoes.Domino.WordRAM.Binary
open ComplexityAbstract.RAM

/-- The magnitude returned by the bit-array absolute-value program agrees
with the mathematical absolute value of every representable signed integer. -/
theorem twos_complement_magnitude (memory : ℕ → ℕ) (base length : ℕ) (z : ℤ)
    (positive : 0< length) (bits : ∀ j< length, memory (base+j)≤1)
    (fits : Fits length z) (encoding : (value memory base length : ℤ)=z%(2^length : ℤ)) :
    (if memory (base+(length-1))=1 then 2^length-value memory base length else value memory base length)=z.natAbs := by
  let half : ℕ := 2^(length-1)
  let cap : ℕ := 2^length
  let unsigned := value memory base length
  have capEq : cap=2*half := by
    dsimp only [cap,half]
    calc
      2^length=2^((length-1)+1) := by congr 1; omega
      _=2*2^(length-1) := by rw [pow_succ]; omega
  have capCast : (cap : ℤ)=2*(half : ℤ) := by exact_mod_cast capEq
  have halfPositive : 0< half := by dsimp only [half]; positivity
  have unsignedBound : unsigned< cap := value_lt memory base length bits
  have lower : -(half : ℤ)≤z := fits.2.1
  have upper : z<(half : ℤ) := fits.2.2
  have encoded : (unsigned : ℤ)=z%(cap : ℤ) := by simpa [unsigned,cap] using encoding
  have lowBound : value memory base (length-1)<half :=
    value_lt memory base (length-1) (fun j hj => bits j (by omega))
  have lastBound := bits (length-1) (by omega)
  have split : unsigned=value memory base (length-1)+memory (base+(length-1))*half := by
    have h := value_succ memory base (length-1)
    rw [show length-1+1=length by omega] at h
    exact h
  by_cases negative : z<0
  · have shiftedNonnegative : 0≤z+(cap : ℤ) := by omega
    have shiftedLt : z+(cap : ℤ)<(cap : ℤ) := by omega
    rw [← Int.add_emod_right z (cap : ℤ),Int.emod_eq_of_lt shiftedNonnegative shiftedLt] at encoded
    have halfLeUnsigned : half≤unsigned := by
      exact_mod_cast (show (half : ℤ)≤(unsigned : ℤ) by omega)
    have sign : memory (base+(length-1))=1 := by
      by_contra different
      have zero : memory (base+(length-1))=0 := by omega
      rw [zero,zero_mul,add_zero] at split
      omega
    rw [if_pos sign]
    change cap-unsigned=z.natAbs
    have absCast := Int.ofNat_natAbs_of_nonpos (Int.le_of_lt negative)
    have subCast : ((cap-unsigned : ℕ) : ℤ)=(cap : ℤ)-unsigned := Int.ofNat_sub (Nat.le_of_lt unsignedBound)
    omega
  · have nonnegative : 0≤z := by omega
    have zLtCap : z<(cap : ℤ) := by omega
    rw [Int.emod_eq_of_lt nonnegative zLtCap] at encoded
    have unsignedLtHalf : unsigned<half := by exact_mod_cast (show (unsigned : ℤ)<(half : ℤ) by omega)
    have sign : memory (base+(length-1))≠1 := by
      intro one
      rw [one,one_mul] at split
      omega
    rw [if_neg sign]
    have absCast := Int.ofNat_natAbs_of_nonneg nonnegative
    change unsigned=z.natAbs
    omega

end LeanTrominoes.Domino.WordRAM.Binary
