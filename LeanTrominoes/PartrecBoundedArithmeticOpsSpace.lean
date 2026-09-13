/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PartrecBoundedArithmetic
import LeanTrominoes.PartrecNatEqualitySpace
import LeanTrominoes.PartrecNatCompareSpace
import LeanTrominoes.PartrecAddSpace
import LeanTrominoes.PartrecMultiplySpace
import LeanTrominoes.PartrecDivisionSpace
import LeanTrominoes.PartrecPowerTwoSpace
import LeanTrominoes.PartrecDynamicDropSpace

/-! # Uniform binary-space envelopes for arithmetic primitives -/

namespace LeanTrominoes.BoundedArithmetic
open Turing Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits

/-- A constant shared by the finite arithmetic instruction set. -/
def arithmeticScale : Nat := 1000000000000000000000000000000000000000000000000000000000000000

def arithmeticBudget (bits : Nat) : Nat := arithmeticScale * (bits+1)

private theorem scaled_sum_bits (a b scale offset bits : Nat)
    (ha : (Computability.encodeNat a).length ≤ bits)
    (hb : (Computability.encodeNat b).length ≤ bits) :
    encodedListSpace [scale*(a+b)+offset]+1 ≤
      2*bits+(Computability.encodeNat scale).length+(Computability.encodeNat offset).length+5 := by
  have h1 := encodeNat_add_length_le_sum a b
  have h2 := encodeNat_mul_length_le_sum scale (a+b)
  have h3 := encodeNat_add_length_le_sum (scale*(a+b)) offset
  simp only [encodedListSpace_cons,encodedListSpace_nil]
  omega

private theorem small_sum_bound (a b bits : Nat)
    (ha : (Computability.encodeNat a).length ≤ bits)
    (hb : (Computability.encodeNat b).length ≤ bits) :
    encodedListSpace [2*(a+b)+4]+1 ≤ 20*(bits+1) := by
  have h := scaled_sum_bits a b 2 4 bits ha hb
  have h2 : (Computability.encodeNat 2).length = 2 := by decide
  have h4 : (Computability.encodeNat 4).length = 3 := by decide
  rw [h2,h4] at h
  omega

private theorem multiply_bound (a b bits : Nat)
    (ha : (Computability.encodeNat a).length ≤ bits)
    (hb : (Computability.encodeNat b).length ≤ bits) :
    encodedListSpace [16*(a+b+a*b+10)+100]+1 ≤ 30*(bits+1) := by
  have hab := encodeNat_add_length_le_sum a b
  have hmul := encodeNat_mul_length_le_sum a b
  have hsum := encodeNat_add_length_le_sum (a+b) (a*b)
  have hten := encodeNat_add_length_le_sum (a+b+a*b) 10
  have hscale := encodeNat_mul_length_le_sum 16 (a+b+a*b+10)
  have hlast := encodeNat_add_length_le_sum (16*(a+b+a*b+10)) 100
  have h10 : (Computability.encodeNat 10).length = 4 := by decide
  have h16 : (Computability.encodeNat 16).length = 5 := by decide
  have h100 : (Computability.encodeNat 100).length = 7 := by decide
  rw [h10] at hten
  rw [h16] at hscale
  rw [h100] at hlast
  simp only [encodedListSpace_cons,encodedListSpace_nil]
  omega

private theorem get_pair_bound (a b bits : Nat) (index : Fin 2)
    (ha : (Computability.encodeNat a).length ≤ bits)
    (hb : (Computability.encodeNat b).length ≤ bits) :
    getCost index.val [a,b] ≤ 100*(bits+1) := by
  have han := listCodeEncodeNat_succ_length_le a
  have hbn := listCodeEncodeNat_succ_length_le b
  simp only [Nat.succ_eq_add_one] at han hbn
  have h0 : (Computability.encodeNat 0).length = 0 := rfl
  fin_cases index <;>
    simp [getCost,dropCost,headCost,idCost,nilCost,tailCost,zeroPrimeCost,succCost,
      encodedListSpace_cons,encodedListSpace_nil,h0] <;> omega

/-- Binary arithmetic executes in a constant multiple of its operand bit bound. -/
theorem Op.code_fits (op : Op) (a b bits : Nat)
    (ha : (Computability.encodeNat a).length ≤ bits)
    (hb : (Computability.encodeNat b).length ≤ bits) :
    EvaluatorCodeFits op.code [a,b] [op.eval a b] (arithmeticBudget bits) := by
  have small := small_sum_bound a b bits ha hb
  cases op with
  | add =>
    apply (natAdd a b).mono
    have cost := natAddCost_le_linear a b
    unfold arithmeticBudget arithmeticScale
    omega
  | sub =>
    apply (subtract a b).mono
    have han := listCodeEncodeNat_succ_length_le a
    have hbn := listCodeEncodeNat_succ_length_le b
    simp only [Nat.succ_eq_add_one] at han hbn
    have h0 : (Computability.encodeNat 0).length = 0 := rfl
    simp [subtractCost,subtractInputCost,subtractLoopCost,prependCost,getCost,dropCost,
      headCost,idCost,nilCost,tailCost,zeroPrimeCost,succCost,
      encodedListSpace_cons,encodedListSpace_nil,h0,arithmeticBudget,arithmeticScale]
    omega
  | mul =>
    apply (natMultiply a b).mono
    have cost := natMultiplyCost_le_linear a b
    have large := multiply_bound a b bits ha hb
    unfold arithmeticBudget arithmeticScale
    omega
  | div | mod =>
    have qbits := (listCodeEncodeNat_length_mono (Nat.div_le_self a b)).trans ha
    have rbits := (listCodeEncodeNat_length_mono (Nat.mod_le a b)).trans ha
    have divided := division a b
    have bound := scaled_sum_bits a b 8 16 bits ha hb
    have h8 : (Computability.encodeNat 8).length = 4 := by decide
    have h16 : (Computability.encodeNat 16).length = 5 := by decide
    rw [h8,h16] at bound
    first
    | apply (comp (get 0 [a/b,a%b]) divided).mono
      have projection := get_pair_bound (a/b) (a%b) bits 0 qbits rbits
      change getCost 0 [a/b,a%b] ≤ 100*(bits+1) at projection
      simp only [divisionSpaceBound,arithmeticBudget,arithmeticScale]
      omega
    | apply (comp (get 1 [a/b,a%b]) divided).mono
      have projection := get_pair_bound (a/b) (a%b) bits 1 qbits rbits
      change getCost 1 [a/b,a%b] ≤ 100*(bits+1) at projection
      simp only [divisionSpaceBound,arithmeticBudget,arithmeticScale]
      omega
  | eq =>
    apply (natEq a b).mono
    have cost := natEqCost_le_linear a b
    unfold arithmeticBudget arithmeticScale
    omega
  | lt =>
    apply (natLt a b).mono
    have cost := natLtCost_le_linear a b
    unfold arithmeticBudget arithmeticScale
    omega

end LeanTrominoes.BoundedArithmetic
