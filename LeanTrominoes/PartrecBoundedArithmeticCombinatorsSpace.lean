/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PartrecBoundedArithmeticOpsSpace
import LeanTrominoes.PartrecBoundedAllSpace

/-! # Linear space envelopes for arithmetic-expression composition -/

namespace LeanTrominoes.BoundedArithmetic
open Turing Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits

theorem idCost_bound (values : List Nat) : idCost values ≤ 10*(encodedListSpace values+1) := by
  have zero : (Computability.encodeNat 0).length = 0 := rfl
  simp [idCost,tailCost,zeroPrimeCost,encodedListSpace_cons,zero]
  omega

theorem headCost_bound (values : List Nat) : headCost values ≤ 10000*(encodedListSpace values+1) := by
  have h := listCodeGetZeroCost_le values
  simp only [getCost,List.drop_zero] at h
  omega

theorem prepend_singleton_bound (values : List Nat) (a b bits ca cb : Nat)
    (ha : (Computability.encodeNat a).length ≤ bits)
    (hb : (Computability.encodeNat b).length ≤ bits) :
    prependCost values [a] [b] ca cb ≤ ca+cb+10*(encodedListSpace values+bits+1) := by
  simp [prependCost,encodedListSpace_cons,encodedListSpace_nil]
  omega

theorem prepend_environment_bound (values : List Nat) (a bits cost : Nat)
    (ha : (Computability.encodeNat a).length ≤ bits) :
    prependCost values [a] values cost (idCost values) ≤ cost+20*(encodedListSpace values+bits+1) := by
  have hid := idCost_bound values
  simp [prependCost,encodedListSpace_cons,encodedListSpace_nil]
  omega

theorem branch_zero_bound (values : List Nat) (test output bits testCost branchCost : Nat)
    (ht : (Computability.encodeNat test).length ≤ bits)
    (ho : (Computability.encodeNat output).length ≤ bits) :
    branchZeroZeroCost values [output] test testCost branchCost ≤
      testCost+branchCost+100*(encodedListSpace values+bits+1) := by
  have h0 : (Computability.encodeNat 0).length = 0 := rfl
  simp [branchZeroZeroCost,branchZeroTestCost,prependCost,idCost,tailCost,zeroPrimeCost,
    encodedListSpace_cons,encodedListSpace_nil,h0]
  omega

theorem branch_succ_bound (values : List Nat) (test output bits testCost branchCost : Nat)
    (ht : (Computability.encodeNat test).length ≤ bits)
    (ho : (Computability.encodeNat output).length ≤ bits) :
    branchZeroSuccCost values [output] test testCost branchCost ≤
      testCost+branchCost+100*(encodedListSpace values+bits+1) := by
  have hp := (listCodeEncodeNat_length_mono (Nat.pred_le test)).trans ht
  simp only [Nat.pred_eq_sub_one] at hp
  have h0 : (Computability.encodeNat 0).length = 0 := rfl
  simp [branchZeroSuccCost,branchZeroTestCost,prependCost,idCost,tailCost,zeroPrimeCost,
    encodedListSpace_cons,encodedListSpace_nil,h0]
  omega

theorem normalize_bound (values : List Nat) (value bits cost : Nat)
    (positive : 1 ≤ bits) (hv : (Computability.encodeNat value).length ≤ bits) :
    normalizeBoolCost values value cost ≤ cost+100000*(encodedListSpace values+bits+1) := by
  have h0 : (Computability.encodeNat 0).length ≤ bits := by change 0 ≤ bits; omega
  have h1 : (Computability.encodeNat 1).length ≤ bits := positive
  have zero := listCodeZeroCost_le_linear values
  by_cases hz : value = 0
  · have bound := branch_zero_bound values value 0 bits cost (zeroCost values) hv h0
    simp only [normalizeBoolCost,if_pos hz]
    omega
  · have bound := branch_succ_bound values value 1 bits cost (oneCost values) hv h1
    have one : oneCost values ≤ 10000*(encodedListSpace values+1)+10 := by
      have z : (Computability.encodeNat 0).length = 0 := rfl
      have o : (Computability.encodeNat 1).length = 1 := rfl
      simp [oneCost,succCost,encodedListSpace_cons,encodedListSpace_nil,z,o]
      omega
    simp only [normalizeBoolCost,if_neg hz]
    omega

theorem normalize_fits {code : ToPartrec.Code} (values : List Nat) (value bits cost : Nat)
    (positive : 1 ≤ bits) (hv : (Computability.encodeNat value).length ≤ bits)
    (fits : EvaluatorCodeFits code values [value] cost) :
    EvaluatorCodeFits (ToPartrec.Code.normalizeBool code) values [(decide (value ≠ 0)).toNat]
      (cost+100000*(encodedListSpace values+bits+1)) := by
  have normalized := (normalizeBool fits).mono (normalize_bound values value bits cost positive hv)
  by_cases hz : value = 0 <;> simpa [hz] using normalized

set_option maxHeartbeats 400000 in
theorem powerTwo_fits (value bits : Nat)
    (hv : (Computability.encodeNat value).length ≤ bits)
    (hp : (Computability.encodeNat (2^value)).length ≤ bits) :
    EvaluatorCodeFits ToPartrec.Code.powerTwoCode [value] [2^value] (arithmeticBudget bits) := by
  apply (powerTwo value).mono
  have next := listCodeEncodeNat_succ_length_le value
  simp only [Nat.succ_eq_add_one] at next
  have h0 : (Computability.encodeNat 0).length = 0 := rfl
  have h1 : (Computability.encodeNat 1).length = 1 := rfl
  simp [powerTwoCost,powerTwoLoopCost,powerTwoInputCost,prependCost,getCost,dropCost,headCost,
    idCost,nilCost,zeroCost,oneCost,tailCost,zeroPrimeCost,succCost,arithmeticBudget,arithmeticScale,
    encodedListSpace_cons,encodedListSpace_nil,h0,h1]
  omega

/-- Dynamic list indexing is linear in retained data and index bits. -/
theorem lookup_fits (values : List Nat) (index bits : Nat)
    (hi : (Computability.encodeNat index).length ≤ bits) :
    EvaluatorCodeFits (ToPartrec.Code.head.comp ToPartrec.Code.dynamicDropCode) (index :: values)
      [values[index]?.getD 0] (10000000*(encodedListSpace values+bits+1)) := by
  have fitted := comp (head (values.drop index)) (dynamicDrop index values)
  have hdrop := dynamicDropSpace_drop_le index values
  have hhead := headCost_bound (values.drop index)
  have cost := dynamicDropCost_le_linear index values
  have bound : headCost (values.drop index)+dynamicDropCost index values ≤
      10000000*(encodedListSpace values+bits+1) := by
    simp only [encodedListSpace_cons] at cost
    omega
  have heq (xs : List Nat) (j : Nat) : (xs.drop j).headI = xs[j]?.getD 0 := by
    induction j generalizing xs with
    | zero => cases xs <;> rfl
    | succ j ih => cases xs with
      | nil => simp
      | cons a xs => simpa using ih xs
  simpa only [heq] using fitted.mono bound

end LeanTrominoes.BoundedArithmetic
