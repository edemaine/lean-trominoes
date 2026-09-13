/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PartrecBoundedArithmeticCombinatorsSpace
import LeanTrominoes.PartrecBooleanSpace

/-! # Coarse workspace rules for guarded Boolean programs -/

namespace Turing.PartrecToTM2.EvaluatorCodeFits
open ToPartrec LeanTrominoes.BoundedArithmetic

theorem boolAnd_bool {left right : Code} {values : List Nat} {a b : Bool} {ca cb : Nat}
    (first : EvaluatorCodeFits left values [a.toNat] ca)
    (last : EvaluatorCodeFits right values [b.toNat] cb) :
    EvaluatorCodeFits (Code.boolAnd left right) values [(a && b).toNat]
      (1000*(encodedListSpace values+ca+cb+2)) := by
  have fit := boolAnd first last
  have eq : (if a.toNat = 0 ∨ b.toNat = 0 then 0 else 1) = (a && b).toNat := by
    cases a <;> cases b <;> rfl
  rw [eq] at fit
  apply fit.mono
  apply boolAndCost_le_budget values a.toNat b.toNat ca cb (encodedListSpace values+ca+cb+1)
  · cases a <;> decide
  · cases b <;> decide
  · omega
  · have h := encodedListSpace_singleton_headI_le values
    simp only [encodedListSpace_cons,encodedListSpace_nil] at h
    omega
  · have h := encodedListSpace_singleton_headI_le values
    have next := encodeNat_succ_length_le values.headI
    simp only [encodedListSpace_cons,encodedListSpace_nil] at h
    simpa only [Nat.succ_eq_add_one] using next.trans (show (Computability.encodeNat values.headI).length+1 ≤ encodedListSpace values+ca+cb+1 by omega)
  · omega
  · omega
  · omega

def guardBudget (space testCost bodyCost : Nat) : Nat :=
  testCost+bodyCost+10000*(space+1)+100*(space+2)

/-- The body needs a space certificate only when the Boolean guard is true. -/
theorem guard_bool {test body : Code} {values : List Nat} {a b : Bool} {ca cb : Nat}
    (testFit : EvaluatorCodeFits test values [a.toNat] ca)
    (bodyFit : a = true → EvaluatorCodeFits body values [b.toNat] cb) :
    EvaluatorCodeFits (Code.branchZero test Code.zero body) values [(a && b).toNat]
      (guardBudget (encodedListSpace values) ca cb) := by
  cases a with
  | false =>
    have fit := branchZero_zero (whenSucc := body) (testValue := 0) rfl testFit (zero values)
    apply fit.mono
    have h := branch_zero_bound values 0 0 1 ca (zeroCost values) (by decide) (by decide)
    have hz := listCodeZeroCost_le_linear values
    unfold guardBudget
    omega
  | true =>
    have fit := branchZero_succ (whenZero := Code.zero) (testValue := 1) (by decide) testFit (bodyFit rfl)
    apply fit.mono
    have bits : (Computability.encodeNat b.toNat).length ≤ 1 := by cases b <;> decide
    have h := branch_succ_bound values 1 b.toNat 1 ca cb (by decide) bits
    unfold guardBudget
    omega

end Turing.PartrecToTM2.EvaluatorCodeFits
