/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PartrecBoundedArithmeticCombinatorsSpace

/-! # A polynomial-space compiler for bounded arithmetic formulas

The formula is fixed finite control. Its safe evaluation premise bounds every
intermediate number in binary, including environments beneath quantifiers.
The resulting machine-space allowance is linear in the input fields and this
bit bound, with a constant depending only on the formula.
-/

namespace LeanTrominoes.BoundedArithmetic
open Turing Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits

def Expr.weight : Expr → Nat
  | .literal n => arithmeticScale * (addConstCost n [0]+1)
  | .load i => arithmeticScale * (i.weight+1)
  | .binary _ a b => arithmeticScale * (a.weight+b.weight+2)
  | .powerTwo a => arithmeticScale * (a.weight+1)
  | .ite t y n => arithmeticScale * (t.weight+y.weight+n.weight+1)
  | .letE a b => arithmeticScale * (a.weight+b.weight+1)
  | .all n b => arithmeticScale * (n.weight+b.weight+1)

set_option maxHeartbeats 2000000 in
theorem Expr.code_fits (expr : Expr) (values : List Nat) (bits : Nat) (positive : 1 ≤ bits)
    (safe : expr.Safe bits values) :
    EvaluatorCodeFits expr.code values [expr.eval values]
      (expr.weight * (encodedListSpace values+bits+1)) := by
  induction expr generalizing values with
  | literal n =>
    apply (numeral n values).mono
    have zero := listCodeZeroCost_le_linear values
    have grow := Nat.mul_le_mul_left (addConstCost n [0]+1)
      (show 1 ≤ encodedListSpace values+bits+1 by omega)
    simp only [numeralCost,Expr.weight,arithmeticScale]
    nlinarith
  | load i ih =>
    have hindex := safe.1.value_bits
    have indexFit := ih values safe.1
    have arguments := prepend indexFit (id values)
    have lookup := lookup_fits values (i.eval values) bits hindex
    have fit := comp lookup arguments
    apply fit.mono
    have prep := prepend_environment_bound values (i.eval values) bits
      (i.weight*(encodedListSpace values+bits+1)) hindex
    simp only [Expr.weight,arithmeticScale]
    nlinarith
  | binary op a b ia ib =>
    have ha := safe.1.value_bits
    have hb := safe.2.1.value_bits
    have arguments := prepend (ia values safe.1) (ib values safe.2.1)
    have fit := comp (op.code_fits (a.eval values) (b.eval values) bits ha hb) arguments
    apply fit.mono
    have prep := prepend_singleton_bound values (a.eval values) (b.eval values) bits
      (a.weight*(encodedListSpace values+bits+1)) (b.weight*(encodedListSpace values+bits+1)) ha hb
    simp only [Expr.weight,arithmeticBudget,arithmeticScale]
    nlinarith
  | powerTwo a ih =>
    have fit := comp (powerTwo_fits (a.eval values) bits safe.1.value_bits safe.2) (ih values safe.1)
    apply fit.mono
    simp only [Expr.weight,arithmeticBudget,arithmeticScale]
    nlinarith
  | ite test yes no it iy ino =>
    have ht := safe.1.value_bits
    have hy := safe.2.1.value_bits
    have hn := safe.2.2.value_bits
    by_cases hz : test.eval values = 0
    · have fitted := branchZero_zero (whenSucc := yes.code) hz (it values safe.1) (ino values safe.2.2)
      have localBound := branch_zero_bound values (test.eval values) (no.eval values) bits
        (test.weight*(encodedListSpace values+bits+1)) (no.weight*(encodedListSpace values+bits+1)) ht hn
      have cost : branchZeroZeroCost values [no.eval values] (test.eval values)
          (test.weight*(encodedListSpace values+bits+1)) (no.weight*(encodedListSpace values+bits+1)) ≤
          (Expr.ite test yes no).weight*(encodedListSpace values+bits+1) := by
        simp only [Expr.weight,arithmeticScale]
        nlinarith
      simpa only [Expr.code,Expr.eval,if_pos hz] using fitted.mono cost
    · have fitted := branchZero_succ (whenZero := no.code) (Nat.pos_of_ne_zero hz)
        (it values safe.1) (iy values safe.2.1)
      have localBound := branch_succ_bound values (test.eval values) (yes.eval values) bits
        (test.weight*(encodedListSpace values+bits+1)) (yes.weight*(encodedListSpace values+bits+1)) ht hy
      have cost : branchZeroSuccCost values [yes.eval values] (test.eval values)
          (test.weight*(encodedListSpace values+bits+1)) (yes.weight*(encodedListSpace values+bits+1)) ≤
          (Expr.ite test yes no).weight*(encodedListSpace values+bits+1) := by
        simp only [Expr.weight,arithmeticScale]
        nlinarith
      simpa only [Expr.code,Expr.eval,if_neg hz] using fitted.mono cost
  | letE a body ia ib =>
    have ha := safe.1.value_bits
    have arguments := prepend (ia values safe.1) (id values)
    have envBound : encodedListSpace (a.eval values :: values)+bits+1 ≤
        2*(encodedListSpace values+bits+1) := by
      simp only [encodedListSpace_cons]
      omega
    have bodyFit := (ib (a.eval values :: values) safe.2).mono
      (Nat.mul_le_mul_left body.weight envBound)
    have fit := comp bodyFit arguments
    apply fit.mono
    have prep := prepend_environment_bound values (a.eval values) bits
      (a.weight*(encodedListSpace values+bits+1)) ha
    simp only [Expr.weight,arithmeticScale]
    nlinarith
  | all count body ic ib =>
    let unit := encodedListSpace values+bits+1
    let leafBudget := (2*body.weight+200000)*unit
    have hc := safe.1.value_bits
    have leafFits (i : Nat) (hi : i ≤ count.eval values) :
        EvaluatorCodeFits (ToPartrec.Code.normalizeBool body.code) (i :: values)
          [(decide (body.eval (i :: values) ≠ 0)).toNat] leafBudget := by
      have hiBits := (listCodeEncodeNat_length_mono hi).trans hc
      have bodySafe := safe.2.2 i hi
      have envBound : encodedListSpace (i :: values)+bits+1 ≤ 2*unit := by
        simp only [encodedListSpace_cons,unit]
        omega
      have bodyFit := (ib (i :: values) bodySafe).mono (Nat.mul_le_mul_left body.weight envBound)
      have normalized := normalize_fits (i :: values) (body.eval (i :: values)) bits
        (body.weight*(2*unit)) positive bodySafe.value_bits bodyFit
      apply normalized.mono
      dsimp [leafBudget]
      nlinarith
    have quantified := boundedAll_uniform values (fun i => decide (body.eval (i :: values) ≠ 0))
      (count.eval values) bits leafBudget hc leafFits
    have arguments := prepend (ic values safe.1) (id values)
    have fit := comp quantified arguments
    apply fit.mono
    have prep := prepend_environment_bound values (count.eval values) bits
      (count.weight*(encodedListSpace values+bits+1)) hc
    simp only [Expr.weight,arithmeticScale]
    dsimp [leafBudget,unit]
    nlinarith

end LeanTrominoes.BoundedArithmetic
