/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFPolySpaceMembership
import LeanTrominoes.PeriodicThreeCNFPolySpaceHardness

/-! # A compiled width guard and PSPACE-completeness of local 1D 3SAT -/
namespace LeanTrominoes.PeriodicCNF.FieldWidth
open BoundedArithmetic BoundedArithmetic.Expr PeriodicCNFFlatEncoding FlatScanner FieldPredicate
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits
open Polynomial

def guardExpr : Expr := .all (var 0)
  (impE (.testBit (var 2) (var 0)) (leE (field 1 (var 0)) 3))

theorem guard_typed (f : PeriodicCNF Nat) :
    guardExpr.Truth (FieldSavitch.suffix f) ↔ f.WidthAtMost 3 := by
  have raw : guardExpr.Truth (FieldSavitch.suffix f) ↔
      ∀ h<(formulaFields f).length, (clauseMarks 1 f.clauses).testBit h = true →
        (formulaFields f)[h]?.getD 0 ≤ 3 := by
    simp only [guardExpr,truth_all,truth_imp,truth_bit,truth_le,FieldSavitch.suffix,
      input,field_eval1]
    simp [context,Expr.eval]
  rw [raw]
  constructor
  · intro check c hc
    obtain ⟨h,hh⟩ := (clauseEntries_members 1 f.clauses c).mpr hc
    have e := check h (clause_bound f hh) ((clauseMarks_testBit _ _ _).mpr ⟨c,hh⟩)
    rwa [clauseEntry_header f hh] at e
  · intro width h _ hh
    obtain ⟨c,hc⟩ := (clauseMarks_testBit _ _ _).mp hh
    rw [clauseEntry_header f hc]
    exact width c ((clauseEntries_members 1 f.clauses c).mp ⟨h,hc⟩)

def guardDecision : Expr := .ite guardExpr 1 0
def widthCheck (f : PeriodicCNF Nat) : Bool := decide (guardExpr.eval (FieldSavitch.suffix f) ≠ 0)

theorem widthCheck_correct (f : PeriodicCNF Nat) : widthCheck f=true ↔ f.WidthAtMost 3 := by
  simpa only [widthCheck,decide_eq_true_eq,Truth] using guard_typed f

theorem guardDecision_eval (f : PeriodicCNF Nat) :
    guardDecision.eval (FieldSavitch.suffix f) = (widthCheck f).toNat := by
  by_cases h : guardExpr.eval (FieldSavitch.suffix f)=0 <;> simp [guardDecision,widthCheck,Expr.eval,h]

def guardCode : Code := guardDecision.code.comp FieldSavitch.suffixCode

def guardCoefficient : Nat :=
  (guardDecision.weight*(guardDecision.radius+1))*(FieldSavitch.suffixCoefficient+1)+FieldSavitch.suffixCoefficient

theorem guardCode_eval (f : PeriodicCNF Nat) :
    guardCode.eval (formulaFields f) = pure [(widthCheck f).toNat] := by
  simp [guardCode,FieldSavitch.suffixCode_eval,Expr.code_eval,guardDecision_eval,Part.bind_eq_bind]

theorem guardCode_fits (f : PeriodicCNF Nat) :
    EvaluatorCodeFits guardCode (formulaFields f) [(widthCheck f).toNat]
      (guardCoefficient*((finEncoding.encode f).length+1)) := by
  have guard := guardDecision.code_fits_automatic (FieldSavitch.suffix f) (by decide)
  rw [guardDecision_eval] at guard
  have init := FieldSavitch.suffixCode_fits f
  rw [← FieldSavitch.fields_space] at init
  have fit := comp_linear guard init
  rw [FieldSavitch.fields_space] at fit
  exact fit

def result (f : PeriodicCNF Nat) : Bool := widthCheck f && FieldSavitch.result f

def decideCode : Code := Code.boolAnd guardCode FieldSavitch.decideCode

theorem result_correct (f : PeriodicCNF Nat) : result f=true ↔ LocalPeriodicThreeCNF1DSAT f := by
  simp [result,Bool.and_eq_true,widthCheck_correct,FieldSavitch.result_correct,LocalPeriodicThreeCNF1DSAT]

theorem decide_eval (f : PeriodicCNF Nat) : decideCode.eval (formulaFields f) = pure [(result f).toNat] := by
  have e := Code.boolAnd_eval_at guardCode FieldSavitch.decideCode (formulaFields f)
    (widthCheck f).toNat (FieldSavitch.result f).toNat (guardCode_eval f) (FieldSavitch.decide_eval f)
  cases ha : widthCheck f <;> cases hb : FieldSavitch.result f <;> simpa [decideCode,result,ha,hb] using e

noncomputable def spacePolynomial : Polynomial Nat :=
  1000*(X+C guardCoefficient*(X+1)+FieldSavitch.spacePolynomial+2)

theorem decide_fits (f : PeriodicCNF Nat) :
    EvaluatorCodeFits decideCode (formulaFields f) [(result f).toNat]
      (spacePolynomial.eval (finEncoding.encode f).length) := by
  have fit := boolAnd_bool (guardCode_fits f) (FieldSavitch.decide_fits f)
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

noncomputable def decider : Complexity.DeciderInPolySpace finEncoding LocalPeriodicThreeCNF1DSAT :=
  deciderInPolySpace_of_flatEvaluatorRunFits formulaFields decodeFormulaFields decodeFormulaFields_formulaFields
    decideCode result result_correct
    (fun f => by rw [decide_eval]; apply Part.mem_some_iff.mpr; cases result f <;> rfl)
    spacePolynomial run_fits

end LeanTrominoes.PeriodicCNF.FieldWidth
namespace LeanTrominoes.PeriodicCNF.PolySpaceHardness

theorem localPeriodicThreeCNF1DSAT_inPSPACE :
    Complexity.InPSPACE PeriodicCNFFlatEncoding.finEncoding LocalPeriodicThreeCNF1DSAT := ⟨FieldWidth.decider⟩

theorem localPeriodicThreeCNF1DSAT_PSPACEComplete :
    Complexity.PSPACEComplete PeriodicCNFFlatEncoding.finEncoding LocalPeriodicThreeCNF1DSAT :=
  ⟨localPeriodicThreeCNF1DSAT_inPSPACE,localPeriodicThreeCNF1DSAT_PSPACEHard⟩

end LeanTrominoes.PeriodicCNF.PolySpaceHardness
