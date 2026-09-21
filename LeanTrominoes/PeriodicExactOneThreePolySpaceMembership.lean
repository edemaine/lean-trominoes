/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicExactOnePolySpaceMembership
import LeanTrominoes.PeriodicThreeSATThreePolySpaceMembership

/-! # Native flat-encoded PSPACE membership for local 1D 1-in-3SAT-3 -/
namespace LeanTrominoes.PeriodicCNF.ExactOneFieldOccurrences
open FieldOccurrences PeriodicCNFFlatEncoding
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits
open Polynomial

def result (f : PeriodicCNF Nat) : Bool := occurrenceCheck f && ExactOneFieldSavitch.result f

def decideCode : Code := Code.boolAnd guardCode ExactOneFieldSavitch.decideCode

theorem result_correct (f : PeriodicCNF Nat) : result f=true ↔ PeriodicExactOneCNF.LocalOneDimensionalThreeSATThree f := by
  simp [result,Bool.and_eq_true,occurrenceCheck_correct,ExactOneFieldSavitch.result_correct,PeriodicExactOneCNF.LocalOneDimensionalThreeSATThree]

theorem decide_eval (f : PeriodicCNF Nat) : decideCode.eval (formulaFields f) = pure [(result f).toNat] := by
  have e := Code.boolAnd_eval_at guardCode ExactOneFieldSavitch.decideCode (formulaFields f)
    (occurrenceCheck f).toNat (ExactOneFieldSavitch.result f).toNat (guardCode_eval f) (ExactOneFieldSavitch.decide_eval f)
  cases ha : occurrenceCheck f <;> cases hb : ExactOneFieldSavitch.result f <;> simpa [decideCode,result,ha,hb] using e

noncomputable def spacePolynomial : Polynomial Nat :=
  1000*(X+C guardCoefficient*(X+1)+ExactOneFieldSavitch.spacePolynomial+2)

theorem decide_fits (f : PeriodicCNF Nat) :
    EvaluatorCodeFits decideCode (formulaFields f) [(result f).toNat]
      (spacePolynomial.eval (finEncoding.encode f).length) := by
  have fit := boolAnd_bool (guardCode_fits f) (ExactOneFieldSavitch.decide_fits f)
  simp only [spacePolynomial,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_C,
    Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one]
  rw [PeriodicCNF.FieldSavitch.fields_space] at fit
  exact fit

theorem run_fits (f : PeriodicCNF Nat) :
    EvaluatorRunFits decideCode (formulaFields f) (spacePolynomial.eval (finEncoding.encode f).length) := by
  let fit := decide_fits f
  let after := EvaluatorExecutionFits.ret_halt fit.output_space
  apply EvaluatorRunFits.of_call
  exact fit.call .halt _ (by simp [continuationSpace,trContStack]) after

noncomputable def decider : Complexity.DeciderInPolySpace finEncoding PeriodicExactOneCNF.LocalOneDimensionalThreeSATThree :=
  deciderInPolySpace_of_flatEvaluatorRunFits formulaFields decodeFormulaFields decodeFormulaFields_formulaFields
    decideCode result result_correct
    (fun f => by rw [decide_eval]; apply Part.mem_some_iff.mpr; cases result f <;> rfl)
    spacePolynomial run_fits

end LeanTrominoes.PeriodicCNF.ExactOneFieldOccurrences
namespace LeanTrominoes.PeriodicExactOneCNF

theorem localOneDimensionalThreeSATThree_inPSPACE :
    Complexity.InPSPACE PeriodicCNFFlatEncoding.finEncoding LocalOneDimensionalThreeSATThree :=
  ⟨PeriodicCNF.ExactOneFieldOccurrences.decider⟩
end LeanTrominoes.PeriodicExactOneCNF
