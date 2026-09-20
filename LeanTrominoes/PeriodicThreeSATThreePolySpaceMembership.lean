/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFFieldWidth
import LeanTrominoes.PeriodicCNFFieldOccurrences

/-! # An encoded polynomial-space decider for local 1D 3SAT-3 -/
namespace LeanTrominoes.PeriodicCNF

def LocalPeriodicThreeSATThree1DSAT (f : PeriodicCNF Nat) : Prop :=
  f.OccurrencesAtMost 3 ∧ LocalPeriodicThreeCNF1DSAT f

namespace FieldOccurrences
open BoundedArithmetic BoundedArithmetic.Expr PeriodicCNFFlatEncoding FlatScanner FieldPredicate
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits
open Polynomial

def guardDecision : Expr := .ite guardExpr 1 0
def occurrenceCheck (f : PeriodicCNF Nat) : Bool := decide (guardExpr.eval (FieldSavitch.suffix f) ≠ 0)

theorem occurrenceCheck_correct (f : PeriodicCNF Nat) : occurrenceCheck f=true ↔ f.OccurrencesAtMost 3 := by
  simpa only [occurrenceCheck,decide_eq_true_eq,Truth,FieldSavitch.suffix] using guard_correct f

theorem guardDecision_eval (f : PeriodicCNF Nat) :
    guardDecision.eval (FieldSavitch.suffix f) = (occurrenceCheck f).toNat := by
  by_cases h : guardExpr.eval (FieldSavitch.suffix f)=0 <;> simp [guardDecision,occurrenceCheck,Expr.eval,h]

def guardCode : Code := guardDecision.code.comp FieldSavitch.suffixCode

def guardCoefficient : Nat :=
  (guardDecision.weight*(guardDecision.radius+1))*(FieldSavitch.suffixCoefficient+1)+FieldSavitch.suffixCoefficient

theorem guardCode_eval (f : PeriodicCNF Nat) :
    guardCode.eval (formulaFields f) = pure [(occurrenceCheck f).toNat] := by
  simp [guardCode,FieldSavitch.suffixCode_eval,Expr.code_eval,guardDecision_eval,Part.bind_eq_bind]

theorem guardCode_fits (f : PeriodicCNF Nat) :
    EvaluatorCodeFits guardCode (formulaFields f) [(occurrenceCheck f).toNat]
      (guardCoefficient*((finEncoding.encode f).length+1)) := by
  have guard := guardDecision.code_fits_automatic (FieldSavitch.suffix f) (by decide)
  rw [guardDecision_eval] at guard
  have init := FieldSavitch.suffixCode_fits f
  rw [← FieldSavitch.fields_space] at init
  have fit := comp_linear guard init
  rw [FieldSavitch.fields_space] at fit
  exact fit

def result (f : PeriodicCNF Nat) : Bool := occurrenceCheck f && FieldWidth.result f

def decideCode : Code := Code.boolAnd guardCode FieldWidth.decideCode

theorem result_correct (f : PeriodicCNF Nat) : result f=true ↔ LocalPeriodicThreeSATThree1DSAT f := by
  simp [result,Bool.and_eq_true,occurrenceCheck_correct,FieldWidth.result_correct,LocalPeriodicThreeSATThree1DSAT]

theorem decide_eval (f : PeriodicCNF Nat) : decideCode.eval (formulaFields f) = pure [(result f).toNat] := by
  have e := Code.boolAnd_eval_at guardCode FieldWidth.decideCode (formulaFields f)
    (occurrenceCheck f).toNat (FieldWidth.result f).toNat (guardCode_eval f) (FieldWidth.decide_eval f)
  cases ha : occurrenceCheck f <;> cases hb : FieldWidth.result f <;> simpa [decideCode,result,ha,hb] using e

noncomputable def spacePolynomial : Polynomial Nat :=
  1000*(X+C guardCoefficient*(X+1)+FieldWidth.spacePolynomial+2)

theorem decide_fits (f : PeriodicCNF Nat) :
    EvaluatorCodeFits decideCode (formulaFields f) [(result f).toNat]
      (spacePolynomial.eval (finEncoding.encode f).length) := by
  have fit := boolAnd_bool (guardCode_fits f) (FieldWidth.decide_fits f)
  simp only [spacePolynomial,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_C,
    Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one]
  rw [FieldSavitch.fields_space] at fit
  exact fit

theorem run_fits (f : PeriodicCNF Nat) :
    EvaluatorRunFits decideCode (formulaFields f) (spacePolynomial.eval (finEncoding.encode f).length) := by
  let fit := decide_fits f
  let after := EvaluatorExecutionFits.ret_halt fit.output_space
  apply EvaluatorRunFits.of_call
  exact fit.call .halt _ (by simp [continuationSpace,trContStack]) after

noncomputable def decider : Complexity.DeciderInPolySpace finEncoding LocalPeriodicThreeSATThree1DSAT :=
  deciderInPolySpace_of_flatEvaluatorRunFits formulaFields decodeFormulaFields decodeFormulaFields_formulaFields
    decideCode result result_correct
    (fun f => by rw [decide_eval]; apply Part.mem_some_iff.mpr; cases result f <;> rfl)
    spacePolynomial run_fits

end FieldOccurrences
namespace PolySpaceHardness

theorem localPeriodicThreeSATThree1DSAT_inPSPACE :
    Complexity.InPSPACE PeriodicCNFFlatEncoding.finEncoding LocalPeriodicThreeSATThree1DSAT :=
  ⟨FieldOccurrences.decider⟩

end PolySpaceHardness
end LeanTrominoes.PeriodicCNF
