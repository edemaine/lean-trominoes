/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolyominoStripSavitchInput
import LeanTrominoes.PartrecGenericSavitchReachSpace

/-! # The strip transition as a certified Savitch leaf -/

namespace LeanTrominoes.PolyominoStripWindow.Savitch
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits FiniteState
open BoundedArithmetic BoundedArithmetic.Expr

/-- A path of length at most one also permits equal endpoints. -/
def baseExpr : Expr := .ite (eqE (var 2) (var 3)) 1 Formula.transitionDecision

def baseCode : Code := baseExpr.code.comp restoreInputCode

def baseExprCoefficient : Nat := baseExpr.weight*(baseExpr.radius+1)
def baseCoefficient : Nat := baseExprCoefficient*(restoreCoefficient+1)+restoreCoefficient

def baseCost (cells : Bool → List Cell) (height bound context count : Nat) (state : DivideEvalState) : Nat :=
  baseCoefficient*(encodedListSpace (GenericSavitchStep.flatProgramList (suffix cells height bound) context count state)+1)

theorem baseExpr_noPower : baseExpr.noPower = true := by
  simp [baseExpr,eqE,Expr.noPower,Formula.transitionDecision_noPower]

theorem baseExpr_eval (cells : Bool → List Cell) (height bound first last : Nat)
    (bounded : Bounded (Raw.tiles cells) bound) :
    baseExpr.eval (Arithmetic.input cells height bound first last) =
      divideBoolTag (decide (first=last) || Raw.check cells height bound first last) := by
  have he : (eqE (var 2) (var 3)).eval (Arithmetic.input cells height bound first last) =
      if first=last then 1 else 0 := rfl
  change (if (eqE (var 2) (var 3)).eval (Arithmetic.input cells height bound first last) = 0 then
    Formula.transitionDecision.eval (Arithmetic.input cells height bound first last) else 1) = _
  rw [he,Formula.transitionDecision_eval cells height bound first last bounded]
  by_cases h : first=last
  · simp [h,divideBoolTag]
  · simp only [h,if_false,ite_true,decide_false,Bool.false_or]
    cases Raw.check cells height bound first last <;> rfl

theorem base_eval (cells : Bool → List Cell) (height bound : Nat)
    (bounded : Bounded (Raw.tiles cells) bound) (context count : Nat) (state : DivideEvalState) :
    baseCode.eval (divideEvalProgramList context count state ++ suffix cells height bound) =
      pure [divideBoolTag (decide (state.query.first=state.query.last) ||
        Raw.check cells height bound state.query.first state.query.last)] := by
  have step : baseCode.eval (divideEvalProgramList context count state ++ suffix cells height bound) =
      baseExpr.code.eval (Arithmetic.input cells height bound state.query.first state.query.last) := by
    simp [baseCode,restoreInput_eval,Part.bind_eq_bind]
  rw [step,Expr.code_eval,baseExpr_eval cells height bound state.query.first state.query.last bounded]

theorem base_fits (cells : Bool → List Cell) (height bound : Nat)
    (bounded : Bounded (Raw.tiles cells) bound) (context count : Nat) (state : DivideEvalState) :
    EvaluatorCodeFits baseCode (GenericSavitchStep.flatProgramList (suffix cells height bound) context count state)
      [divideBoolTag (decide (state.query.first=state.query.last) || Raw.check cells height bound state.query.first state.query.last)]
      (baseCost cells height bound context count state) := by
  have leaf := baseExpr.code_fits_automatic
    (Arithmetic.input cells height bound state.query.first state.query.last) baseExpr_noPower
  rw [baseExpr_eval cells height bound state.query.first state.query.last bounded] at leaf
  have inputFit := restoreInput_fits cells height bound context count state
  exact comp_linear leaf inputFit

end LeanTrominoes.PolyominoStripWindow.Savitch
