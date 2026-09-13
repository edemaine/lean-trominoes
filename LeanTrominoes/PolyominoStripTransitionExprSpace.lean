/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolyominoStripTransitionExpr

/-! # An actual evaluator-space certificate for the variable-tile transition -/

namespace LeanTrominoes.PolyominoStripWindow.Formula
open BoundedArithmetic BoundedArithmetic.Expr Turing.PartrecToTM2

/-- Normalize the formula's truth value to the standard Boolean output field. -/
def transitionDecision : Expr := .ite transition 1 0

theorem transitionDecision_eval (cells : Bool → List Cell) (height bound first second : Nat)
    (bounded : Bounded (Raw.tiles cells) bound) :
    transitionDecision.eval (Arithmetic.input cells height bound first second) =
      (Raw.check cells height bound first second).toNat := by
  have correct := transition_truth cells height bound first second bounded
  unfold Truth at correct
  by_cases h : transition.eval (Arithmetic.input cells height bound first second) = 0
  · have no : ¬ Raw.Transition cells height bound first second := by simpa [h] using correct.symm
    simp [transitionDecision,Expr.eval,h,Raw.check,no]
  · have yes := correct.mp h
    simp [transitionDecision,Expr.eval,h,Raw.check,yes]

theorem transitionDecision_noPower : transitionDecision.noPower = true := by
  simp [transitionDecision,Expr.noPower,transition_noPower]

/-- This constant depends on the fixed checker, never on the tiles or strip. -/
def transitionSpaceConstant : Nat := transitionDecision.weight*(transitionDecision.radius+1)

theorem transition_code_eval (cells : Bool → List Cell) (height bound first second : Nat)
    (bounded : Bounded (Raw.tiles cells) bound) :
    transitionDecision.code.eval (Arithmetic.input cells height bound first second) =
      pure [(Raw.check cells height bound first second).toNat] := by
  rw [Expr.code_eval,transitionDecision_eval cells height bound first second bounded]

/-- All placements and cells are checked using linear space in the binary input fields. -/
theorem transition_code_fits (cells : Bool → List Cell) (height bound first second : Nat)
    (bounded : Bounded (Raw.tiles cells) bound) :
    EvaluatorCodeFits transitionDecision.code (Arithmetic.input cells height bound first second)
      [(Raw.check cells height bound first second).toNat]
      (transitionSpaceConstant*(encodedListSpace (Arithmetic.input cells height bound first second)+1)) := by
  have fit := transitionDecision.code_fits_automatic
    (Arithmetic.input cells height bound first second) transitionDecision_noPower
  rw [transitionDecision_eval cells height bound first second bounded] at fit
  exact fit

end LeanTrominoes.PolyominoStripWindow.Formula
