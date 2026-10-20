/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMSigned

/-! # Raw binary input fields

Encoding an integer supplies its bits, not any determinant, decoded neighbor,
or solver output. All fields have a declared common precision.
-/
namespace LeanTrominoes.Domino.WordRAM.Binary

/-- Exactly `length` little-endian bits, including high zero padding. -/
def digits : ℕ → ℕ → List ℕ
  | 0,_ => []
  | length+1,n => n%2::digits length (n/2)

@[simp] theorem digits_length (length n : ℕ) : (digits length n).length=length := by
  induction length generalizing n <;> simp_all [digits]

theorem digits_mem (length n : ℕ) : ∀ bit∈digits length n, bit≤1 := by
  induction length generalizing n with
  | zero => simp [digits]
  | succ length ih =>
    intro bit member
    simp only [digits,List.mem_cons] at member
    rcases member with same | rest
    · subst bit
      omega
    · exact ih (n/2) bit rest

def digitsMemory (length n : ℕ) (index : ℕ) : ℕ := (digits length n)[index]?.getD 0

theorem digitsMemory_bits (length n index : ℕ) : digitsMemory length n index≤1 := by
  unfold digitsMemory
  cases found : (digits length n)[index]? with
  | none => simp
  | some bit =>
    simp only [Option.getD_some]
    exact digits_mem length n bit (List.mem_of_getElem? found)

/-- Exact value of the raw bit encoding, including possible truncation. -/
theorem digits_value (length n : ℕ) : value (digitsMemory length n) 0 length=n%2^length := by
  induction length generalizing n with
  | zero => simp [Nat.mod_one]
  | succ length ih =>
    rw [value_head]
    have head : digitsMemory (length+1) n 0=n%2 := by rfl
    have tail : value (digitsMemory (length+1) n) (0+1) length=
        value (digitsMemory length (n/2)) 0 length := by
      unfold value
      apply Finset.sum_congr rfl
      intro i hi
      simp [digitsMemory,digits,Nat.one_add]
    rw [head,tail,ih,pow_succ',Nat.mod_mul]

/-- The nonnegative representative used for two's-complement bit input. -/
def unsigned (length : ℕ) (z : ℤ) : ℕ := (z%(2^length : ℤ)).toNat

def integerDigits (length : ℕ) (z : ℤ) : List ℕ := digits length (unsigned length z)

theorem unsigned_lt (length : ℕ) (z : ℤ) : unsigned length z<2^length := by
  have nonnegative := Int.emod_nonneg z (by positivity : (2^length : ℤ)≠0)
  have less := Int.emod_lt_of_pos z (by positivity : (0:ℤ)<2^length)
  unfold unsigned
  exact (Int.toNat_lt nonnegative).mpr (by exact_mod_cast less)

theorem unsigned_cast (length : ℕ) (z : ℤ) : (unsigned length z : ℤ)=z%(2^length : ℤ) := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg z (by positivity))

theorem integerDigits_value (length : ℕ) (z : ℤ) :
    (value (digitsMemory length (unsigned length z)) 0 length : ℤ)=z%(2^length : ℤ) := by
  rw [digits_value,Nat.mod_eq_of_lt (unsigned_lt length z),unsigned_cast]

end LeanTrominoes.Domino.WordRAM.Binary
