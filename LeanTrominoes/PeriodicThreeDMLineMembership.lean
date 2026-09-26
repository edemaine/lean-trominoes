/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeDMFieldEvaluator
import LeanTrominoes.PeriodicThreeDMCoreGuard
import LeanTrominoes.PeriodicThreeDMDegreeGuard
import LeanTrominoes.PartrecFlatFieldPolySpace
import LeanTrominoes.PartrecBooleanUniformSpace

/-! # Native PSPACE membership of local one-dimensional degree-two-or-three 3DM -/
noncomputable section
namespace LeanTrominoes.PeriodicThreeDM.NativeLine
open FlatEncoding BoundedArithmetic BoundedArithmetic.Expr
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits Polynomial

def guard : Expr := andE CoreGuard.core DegreeGuard.guard
def decision : Expr := .ite guard 1 0
def metadata (p : PeriodicThreeDM) : Bool := decide (guard.eval (fields p) ≠ 0)

theorem metadata_correct (p : PeriodicThreeDM) : metadata p = true ↔
    p.IsWellFormed ∧ p.DegreeTwoOrThree ∧ p.IsOneDimensional ∧ p.IsLocal := by
  simp only [metadata,decide_eq_true_eq]
  change guard.Truth (fields p) ↔ _
  rw [guard,truth_and,CoreGuard.core_truth,DegreeGuard.guard_truth]
  tauto

theorem decision_eval (p : PeriodicThreeDM) : decision.eval (fields p) = (metadata p).toNat := by
  by_cases h : guard.eval (fields p)=0 <;> simp [decision,Expr.eval,metadata,h]

theorem decision_noPower : decision.noPower = true := by
  simp [decision,guard,andE,Expr.noPower,CoreGuard.core_noPower,DegreeGuard.guard_noPower]

def coefficient : Nat := decision.weight*(decision.radius+1)

theorem metadata_fits (p : PeriodicThreeDM) :
    EvaluatorCodeFits decision.code (fields p) [(metadata p).toNat]
      (coefficient*((finEncoding.encode p).length+1)) := by
  have fit := decision.code_fits_automatic (fields p) decision_noPower
  rw [decision_eval,FieldSavitch.fields_space] at fit
  exact fit

def code : Code := Code.boolAnd decision.code FieldSavitch.decideCode
def result (p : PeriodicThreeDM) : Bool := metadata p && FieldSavitch.result p

def space : Polynomial Nat := 1000*(X+C coefficient*(X+1)+FieldSavitch.spacePolynomial+2)

theorem result_correct (p : PeriodicThreeDM) : result p = true ↔ LocalLineProblem p := by
  rw [result,Bool.and_eq_true,metadata_correct]
  constructor
  · rintro ⟨⟨wf,degree,horizontal,locality⟩,sat⟩
    exact ⟨wf,degree,horizontal,locality,(FieldSavitch.result_correct p horizontal locality).mp sat⟩
  · rintro ⟨wf,degree,horizontal,locality,sat⟩
    exact ⟨⟨wf,degree,horizontal,locality⟩,(FieldSavitch.result_correct p horizontal locality).mpr sat⟩

theorem code_eval (p : PeriodicThreeDM) : code.eval (fields p) = pure [(result p).toNat] := by
  have guardEval : decision.code.eval (fields p) = pure [(metadata p).toNat] := by rw [Expr.code_eval,decision_eval]
  have h := Code.boolAnd_eval_at decision.code FieldSavitch.decideCode (fields p)
    (metadata p).toNat (FieldSavitch.result p).toNat guardEval (FieldSavitch.decide_eval p)
  cases ha : metadata p <;> cases hb : FieldSavitch.result p <;> simpa [code,result,ha,hb] using h

theorem code_fits (p : PeriodicThreeDM) :
    EvaluatorCodeFits code (fields p) [(result p).toNat] (space.eval (finEncoding.encode p).length) := by
  have fit := boolAnd_bool (metadata_fits p) (FieldSavitch.decide_fits p)
  rw [FieldSavitch.fields_space] at fit
  simpa only [code,result,space,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_C,
    Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one] using fit

def decider : Complexity.DeciderInPolySpace finEncoding LocalLineProblem :=
  deciderInPolySpace_of_flatEvaluatorRunFits fields decodeFields decodeFields_fields code result result_correct
    (fun p => by rw [code_eval]; apply Part.mem_some_iff.mpr; cases result p <;> rfl)
    space (fun p => by
      let fit := code_fits p
      let after := EvaluatorExecutionFits.ret_halt fit.output_space
      apply EvaluatorRunFits.of_call
      exact fit.call .halt _ (by simp [finEncoding,continuationSpace,trContStack]) after)

end LeanTrominoes.PeriodicThreeDM.NativeLine
namespace LeanTrominoes.PeriodicThreeDM

theorem localLineProblem_inPSPACE : Complexity.InPSPACE FlatEncoding.finEncoding LocalLineProblem := ⟨NativeLine.decider⟩

end LeanTrominoes.PeriodicThreeDM
end
