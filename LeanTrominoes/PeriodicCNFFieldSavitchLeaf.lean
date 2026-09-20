/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFFieldSavitchInput
import LeanTrominoes.PartrecGenericSavitchReachSpace

/-! # The CNF transition as a certified Savitch leaf -/

namespace LeanTrominoes.PeriodicCNF.FieldSavitch
open PolyominoStripWindow.Savitch
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits FiniteState
open BoundedArithmetic BoundedArithmetic.Expr

theorem decision_code_eval (f : PeriodicCNF Nat) (a b : Nat) :
    FieldPredicate.decision.code.eval (FieldPredicate.input f a b) = pure [(FieldPredicate.check f a b).toNat] := by
  rw [Expr.code_eval,FieldPredicate.decision_eval]

/-- A path of length at most one also permits equal endpoints. -/
def decisionCoefficient : Nat := FieldPredicate.decision.weight*(FieldPredicate.decision.radius+1)

theorem decision_code_fits (f : PeriodicCNF Nat) (a b : Nat) :
    EvaluatorCodeFits FieldPredicate.decision.code (FieldPredicate.input f a b) [(FieldPredicate.check f a b).toNat]
      (decisionCoefficient*(encodedListSpace (FieldPredicate.input f a b)+1)) := by
  have fit := FieldPredicate.decision.code_fits_automatic (FieldPredicate.input f a b) FieldPredicate.decision_noPower
  rw [FieldPredicate.decision_eval] at fit
  exact fit

def baseExpr : Expr := .ite (eqE (var 3) (var 4)) 1 FieldPredicate.decision

def baseCode : Code := baseExpr.code.comp restoreInputCode

def baseExprCoefficient : Nat := baseExpr.weight*(baseExpr.radius+1)
def baseCoefficient : Nat := baseExprCoefficient*(restoreCoefficient+1)+restoreCoefficient

def baseCost (f : PeriodicCNF Nat) (context count : Nat) (state : DivideEvalState) : Nat :=
  baseCoefficient*(encodedListSpace (GenericSavitchStep.flatProgramList (suffix f) context count state)+1)

theorem baseExpr_noPower : baseExpr.noPower = true := by
  simp [baseExpr,eqE,Expr.noPower,FieldPredicate.decision_noPower]

theorem baseExpr_eval (f : PeriodicCNF Nat) (first last : Nat) :
    baseExpr.eval (FieldPredicate.input f first last) =
      divideBoolTag (decide (first=last) || FieldPredicate.check f first last) := by
  have he : (eqE (var 3) (var 4)).eval (FieldPredicate.input f first last) =
      if first=last then 1 else 0 := rfl
  change (if (eqE (var 3) (var 4)).eval (FieldPredicate.input f first last) = 0 then
    FieldPredicate.decision.eval (FieldPredicate.input f first last) else 1) = _
  rw [he,FieldPredicate.decision_eval f first last]
  by_cases h : first=last
  · simp [h,divideBoolTag]
  · simp only [h,if_false,ite_true,decide_false,Bool.false_or]
    cases FieldPredicate.check f first last <;> rfl

theorem base_eval (f : PeriodicCNF Nat)
    (context count : Nat) (state : DivideEvalState) :
    baseCode.eval (divideEvalProgramList context count state ++ suffix f) =
      pure [divideBoolTag (decide (state.query.first=state.query.last) ||
        FieldPredicate.check f state.query.first state.query.last)] := by
  have step : baseCode.eval (divideEvalProgramList context count state ++ suffix f) =
      baseExpr.code.eval (FieldPredicate.input f state.query.first state.query.last) := by
    simp [baseCode,restoreInput_eval,Part.bind_eq_bind]
  rw [step,Expr.code_eval,baseExpr_eval f state.query.first state.query.last]

theorem base_fits (f : PeriodicCNF Nat)
    (context count : Nat) (state : DivideEvalState) :
    EvaluatorCodeFits baseCode (GenericSavitchStep.flatProgramList (suffix f) context count state)
      [divideBoolTag (decide (state.query.first=state.query.last) || FieldPredicate.check f state.query.first state.query.last)]
      (baseCost f context count state) := by
  have leaf := baseExpr.code_fits_automatic
    (FieldPredicate.input f state.query.first state.query.last) baseExpr_noPower
  rw [baseExpr_eval f state.query.first state.query.last] at leaf
  have inputFit := restoreInput_fits f context count state
  exact comp_linear leaf inputFit

end LeanTrominoes.PeriodicCNF.FieldSavitch
