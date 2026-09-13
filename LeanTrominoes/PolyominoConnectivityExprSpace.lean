/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolyominoConnectivityExpr

/-! # Linear evaluator workspace for the full disconnectedness test -/

namespace LeanTrominoes.PolyominoConnectivitySearch.Formula
open BoundedArithmetic BoundedArithmetic.Expr PolyominoStripWindow Turing.PartrecToTM2

def disconnectedDecision : Expr := .ite disconnected 1 0

def disconnectedSpaceConstant : Nat := disconnectedDecision.weight*(disconnectedDecision.radius+1)

theorem disconnectedDecision_eval (cells : Bool → List Cell) (height bound second : Nat)
    (nonempty : cells true ≠ []) :
    disconnectedDecision.eval (Arithmetic.input cells height bound (2^(cells true).length) second) =
      (disconnectedPacked (cells true)).toNat := by
  have correct := (disconnected_truth cells height bound second nonempty).trans
    (disconnectedPacked_correct (cells true) nonempty).symm
  unfold Truth at correct
  by_cases h : disconnected.eval (Arithmetic.input cells height bound (2^(cells true).length) second) = 0
  · have no : disconnectedPacked (cells true) = false := by
      have notTrue : ¬ disconnectedPacked (cells true) = true := by simpa [h] using correct.symm
      exact Bool.eq_false_iff.mpr notTrue
    simp [disconnectedDecision,Expr.eval,h,no]
  · have yes := correct.mp h
    simp [disconnectedDecision,Expr.eval,h,yes]

theorem disconnectedDecision_noPower : disconnectedDecision.noPower = true := by
  simp [disconnectedDecision,Expr.noPower,disconnected_noPower]

theorem disconnected_code_eval (cells : Bool → List Cell) (height bound second : Nat)
    (nonempty : cells true ≠ []) :
    disconnectedDecision.code.eval (Arithmetic.input cells height bound (2^(cells true).length) second) =
      pure [(disconnectedPacked (cells true)).toNat] := by
  rw [Expr.code_eval,disconnectedDecision_eval cells height bound second nonempty]

theorem disconnected_code_fits (cells : Bool → List Cell) (height bound second : Nat)
    (nonempty : cells true ≠ []) :
    EvaluatorCodeFits disconnectedDecision.code
      (Arithmetic.input cells height bound (2^(cells true).length) second)
      [(disconnectedPacked (cells true)).toNat]
      (disconnectedSpaceConstant*(encodedListSpace
        (Arithmetic.input cells height bound (2^(cells true).length) second)+1)) := by
  have fit := disconnectedDecision.code_fits_automatic
    (Arithmetic.input cells height bound (2^(cells true).length) second) disconnectedDecision_noPower
  rw [disconnectedDecision_eval cells height bound second nonempty] at fit
  exact fit

end LeanTrominoes.PolyominoConnectivitySearch.Formula
