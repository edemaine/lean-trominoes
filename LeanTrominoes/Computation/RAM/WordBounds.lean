/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ComplexityAbstract
import Mathlib.Data.Nat.Log
import Mathlib.Data.Int.Order.Basic
import Mathlib.Tactic

/-! # Signed word bounds from polynomial magnitude bounds

The bounds concern representable values. They do not turn an instrumented
cost counter into a machine execution certificate.
-/
namespace LeanTrominoes.WordBounds

/-- Enlarging the word size preserves representability. -/
theorem fits_mono {small large : ℕ} {x : ℤ} (width : small≤large)
    (fits : ComplexityAbstract.RAM.Fits small x) : ComplexityAbstract.RAM.Fits large x := by
  have powers : (2:ℤ)^(small-1) ≤ 2^(large-1) :=
    pow_le_pow_right₀ (by decide) (Nat.sub_le_sub_right width 1)
  exact ⟨fits.1.trans_le width, (neg_le_neg powers).trans fits.2.1, fits.2.2.trans_le powers⟩

/-- A natural-number magnitude budget needs one sign bit beyond its binary length. -/
def bits (bound : ℕ) : ℕ := Nat.log2 (bound+1)+2

theorem fits_of_natAbs_le (bound : ℕ) (x : ℤ) (h : x.natAbs ≤ bound) :
    ComplexityAbstract.RAM.Fits (bits bound) x := by
  have power : bound < 2^(Nat.log2 (bound+1)+1) :=
    (Nat.lt_succ_self bound).trans (Nat.lt_log2_self (n := bound+1))
  have magnitude : x.natAbs < 2^(Nat.log2 (bound+1)+1) := h.trans_lt power
  have abs : (x.natAbs : ℤ) < (2:ℤ)^(Nat.log2 (bound+1)+1) := by exact_mod_cast magnitude
  change 0<Nat.log2 (bound+1)+2 ∧
    -(2^(Nat.log2 (bound+1)+2-1) : ℤ) ≤ x ∧ x < (2^(Nat.log2 (bound+1)+2-1) : ℤ)
  rw [Int.natCast_natAbs] at abs
  have both := abs_lt.mp abs
  exact ⟨by omega,by simpa using both.1.le,by simpa using both.2⟩

/-- Every polynomial magnitude bound gives a word requirement O(log(size+2)),
with an explicit constant overhead and an explicit logarithmic coefficient. -/
theorem polynomial_fits (C exponent size : ℕ) (x : ℤ)
    (h : x.natAbs ≤ C*(size+1)^exponent) :
    ComplexityAbstract.RAM.Fits
      (Nat.log2 (C+1)+2+exponent*(Nat.log2 (size+1)+1)) x := by
  have hc : C < 2^(Nat.log2 (C+1)+1) :=
    (Nat.lt_succ_self C).trans (Nat.lt_log2_self (n := C+1))
  have hn : size+1 ≤ 2^(Nat.log2 (size+1)+1) := (Nat.lt_log2_self (n := size+1)).le
  have hp := Nat.pow_le_pow_left hn exponent
  have prod : C*(size+1)^exponent <
      2^(Nat.log2 (C+1)+1+exponent*(Nat.log2 (size+1)+1)) := by
    calc
      _ < 2^(Nat.log2 (C+1)+1)*(size+1)^exponent :=
        Nat.mul_lt_mul_of_pos_right hc (Nat.pow_pos (by omega))
      _ ≤ 2^(Nat.log2 (C+1)+1)*(2^(Nat.log2 (size+1)+1))^exponent := Nat.mul_le_mul_left _ hp
      _ = _ := by rw [← pow_mul,← pow_add]; congr 1; rw [Nat.mul_comm (Nat.log2 (size+1)+1) exponent]
  have magnitude := h.trans_lt prod
  have abs : (x.natAbs : ℤ) < (2:ℤ)^(Nat.log2 (C+1)+1+exponent*(Nat.log2 (size+1)+1)) := by
    exact_mod_cast magnitude
  rw [Int.natCast_natAbs] at abs
  have both := abs_lt.mp abs
  have same : Nat.log2 (C+1)+2+exponent*(Nat.log2 (size+1)+1)-1 =
      Nat.log2 (C+1)+1+exponent*(Nat.log2 (size+1)+1) := by omega
  refine ⟨by omega,?_,?_⟩
  · rw [same]
    exact both.1.le
  · rw [same]
    exact both.2

/-- A polynomial magnitude bound fits every word size above an explicit
constant multiple of log₂(size+2). -/
theorem polynomial_fits_uniform (C exponent size w : ℕ) (x : ℤ)
    (width : (Nat.log2 (C+1)+2*exponent)*Nat.log2 (size+2)+2≤w)
    (h : x.natAbs≤C*(size+1)^exponent) : ComplexityAbstract.RAM.Fits w x := by
  have lower : 1≤Nat.log2 (size+2) := by
    have h := Nat.log_mono_right (b := 2) (show 2≤size+2 by omega)
    simpa [← Nat.log2_eq_log_two] using h
  have upper : Nat.log2 (size+1)≤Nat.log2 (size+2) := by
    simpa only [Nat.log2_eq_log_two] using (Nat.log_mono_right (b := 2) (show size+1≤size+2 by omega))
  apply fits_mono (large := w) ?_ (polynomial_fits C exponent size x h)
  have term := Nat.mul_le_mul_left exponent (show Nat.log2 (size+1)+1≤2*Nat.log2 (size+2) by omega)
  have constant := Nat.mul_le_mul_left (Nat.log2 (C+1)) lower
  nlinarith

/-- A signed input word has magnitude at most 2^w. The looser unsigned bound
also covers the most negative signed value. -/
theorem natAbs_le_of_fits {w : ℕ} {value : ℤ} (fits : ComplexityAbstract.RAM.Fits w value) :
    value.natAbs≤2^w := by
  have power : (2:ℤ)^(w-1)≤2^w := pow_le_pow_right₀ (by decide) (by omega)
  have abs : |value|≤(2:ℤ)^w := abs_le.mpr
    ⟨(neg_le_neg power).trans fits.2.1,fits.2.2.le.trans power⟩
  rw [← Int.natCast_natAbs] at abs
  exact_mod_cast abs

/-- Polynomial arithmetic in w-bit input entries needs only a constant number
of w-bit words. The constant depends on the polynomial, not on w or the entries.
This is a precision bound, not a multiword arithmetic implementation. -/
theorem polynomial_fits_words (C exponent w : ℕ) (value : ℤ) (positive : 0<w)
    (h : value.natAbs≤C*(2^w+1)^exponent) :
    ComplexityAbstract.RAM.Fits ((Nat.log2 (C+1)+2+3*exponent)*w) value := by
  have powerPositive : 1≤(2:ℕ)^w := Nat.one_le_two_pow
  have logBound : Nat.log2 (2^w+1)≤w+1 := by
    have bound : 2^w+1<2^(w+2) := by
      rw [pow_add]
      norm_num
      omega
    exact Nat.le_of_lt_succ ((Nat.log2_lt (by omega : 2^w+1≠0)).mpr bound)
  apply fits_mono (large := (Nat.log2 (C+1)+2+3*exponent)*w) ?_
    (polynomial_fits C exponent (2^w) value h)
  have scaled := Nat.mul_le_mul_left exponent (show Nat.log2 (2^w+1)+1≤3*w by omega)
  have constant := Nat.mul_le_mul_left (Nat.log2 (C+1)+2) (show 1≤w by omega)
  nlinarith

end LeanTrominoes.WordBounds
