/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMAddition

/-! # Numeric facts for the binary RAM representation -/
namespace LeanTrominoes.Domino.WordRAM.Binary

/-- A length-L binary array has value strictly below 2^L. The digit bound,
not a machine-word bound on the interpreted integer, is the hypothesis. -/
theorem value_lt (memory : ℕ → ℕ) (base length : ℕ)
    (bits : ∀ i< length, memory (base+i)≤1) : value memory base length<2^length := by
  induction length with
  | zero => simp
  | succ length ih =>
    have earlier := ih (fun i hi => bits i (by omega))
    have last := bits length (by omega)
    rw [value_succ,pow_succ]
    nlinarith

/-- Pointwise Boolean complementation represents arithmetic subtraction from
an all-ones binary word of arbitrary precision. -/
theorem complement_value (memory : ℕ → ℕ) (base length : ℕ)
    (bits : ∀ i< length, memory (base+i)≤1) :
    value (fun a => 1-memory a) base length+value memory base length=2^length-1 := by
  induction length with
  | zero => simp
  | succ length ih =>
    have earlier := ih (fun i hi => bits i (by omega))
    have last := bits length (by omega)
    rw [value_succ,value_succ,pow_succ]
    have bit : 1-memory (base+length)+memory (base+length)=1 := Nat.sub_add_cancel last
    have scaled := congrArg (fun n : ℕ => n*2^length) bit
    have power : 1≤(2:ℕ)^length := Nat.one_le_two_pow
    have old : value (fun a => 1-memory a) base length+value memory base length+1=2^length := by omega
    have larger : 1≤2^length*2 := by omega
    have recover := Nat.sub_add_cancel larger
    nlinarith only [old,scaled,recover]

/-- In binary subtraction, final carry one is precisely the unsigned
comparison test. This is the test used by long division. -/
theorem subtract_carry_iff (first second result carry length : ℕ)
    (firstBound : first<2^length) (secondBound : second<2^length)
    (resultBound : result<2^length) (carryBound : carry≤1)
    (equation : result+second+carry*2^length=first+2^length) :
    carry=1 ↔ second≤first := by
  constructor
  · intro equal
    subst carry
    omega
  · intro ordered
    by_contra different
    have zero : carry=0 := by omega
    rw [zero,zero_mul] at equation
    omega

/-- If no borrow occurs, the low digits are the exact difference. -/
theorem subtract_no_borrow (first second result carry length : ℕ)
    (firstBound : first<2^length) (secondBound : second<2^length)
    (resultBound : result<2^length) (carryBound : carry≤1)
    (equation : result+second+carry*2^length=first+2^length)
    (ordered : second≤first) : result=first-second := by
  have c := (subtract_carry_iff first second result carry length firstBound secondBound resultBound carryBound equation).mpr ordered
  rw [c] at equation
  omega

/-- The one-bit reduction step of binary long division. Its two branches
require only a binary subtraction and its final-carry comparison. -/
def remainderStep (denominator remainder bit : ℕ) : ℕ :=
  let next := 2*remainder+bit
  if denominator≤next then next-denominator else next

theorem remainderStep_lt {denominator remainder bit : ℕ}
    (positive : 0< denominator) (old : remainder< denominator) (binary : bit≤1) :
    remainderStep denominator remainder bit< denominator := by
  dsimp only [remainderStep]
  split_ifs <;> omega

theorem remainderStep_eq_mod {denominator remainder bit : ℕ}
    (positive : 0< denominator) (old : remainder< denominator) (binary : bit≤1) :
    remainderStep denominator remainder bit=(2*remainder+bit)%denominator := by
  dsimp only [remainderStep]
  split_ifs with subtract
  · have bound : 2*remainder+bit<denominator+denominator := by omega
    rw [Nat.mod_eq_sub_mod subtract,Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]

/-- Replacing a prefix by its remainder commutes with appending one bit. -/
theorem remainderStep_prefix (denominator prior bit : ℕ) (positive : 0< denominator) (binary : bit≤1) :
    remainderStep denominator (prior%denominator) bit=(2*prior+bit)%denominator := by
  rw [remainderStep_eq_mod positive (Nat.mod_lt _ positive) binary]
  simp [Nat.add_mod,Nat.mul_mod]

/-- The opposite carry convention used by the direct borrow routine. -/
theorem borrow_zero_iff (first second result borrow length : ℕ)
    (resultBound : result<2^length) (borrowBound : borrow≤1)
    (equation : result+second=first+borrow*2^length) :
    borrow=0 ↔ second≤first := by
  constructor
  · intro zero
    rw [zero,zero_mul] at equation
    omega
  · intro ordered
    by_contra different
    have one : borrow=1 := by omega
    rw [one,one_mul] at equation
    omega

theorem borrow_zero_result (first second result borrow length : ℕ)
    (equation : result+second=first+borrow*2^length) (zero : borrow=0) :
    result=first-second := by
  rw [zero,zero_mul] at equation
  omega

/-- Splitting off the least significant bit of an array interpretation. -/
theorem value_head (memory : ℕ → ℕ) (base length : ℕ) :
    value memory base (length+1)=memory base+2*value memory (base+1) length := by
  induction length with
  | zero => simp [value_succ]
  | succ length ih =>
    rw [value_succ,ih,value_succ,pow_succ]
    rw [show base+(length+1)=base+1+length by omega]
    ring

/-- Scanning an array from its high end appends one binary digit to the
previous high prefix. -/
theorem value_suffix_step (memory : ℕ → ℕ) (base count i : ℕ) (within : i< count) :
    value memory (base+i) (count-i)=memory (base+i)+2*value memory (base+(i+1)) (count-(i+1)) := by
  rw [show count-i=count-(i+1)+1 by omega,value_head]
  congr 2 <;> omega

end LeanTrominoes.Domino.WordRAM.Binary
