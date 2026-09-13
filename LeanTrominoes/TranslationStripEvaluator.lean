/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Theorem55StripEvaluator
import LeanTrominoes.TranslationStripSearchSetup
import LeanTrominoes.TranslationStripDecider

/-! # Polynomial-space translation-only strip Evaluator -/

namespace LeanTrominoes.TranslationStrip.Evaluator
open Theorem55StripDecider Theorem55StripDecider.Evaluator

open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits
open PolyominoStripWindow BoundedArithmetic BoundedArithmetic.Expr

def bodyCode : Code := Code.boolAnd PolyominoStripWindow.Savitch.cutCode TranslationStrip.Savitch.searchCode
def suffixDecisionCode : Code := Code.branchZero guardExpr.code Code.zero bodyCode
def decideCode : Code := suffixDecisionCode.comp suffixCode

def bodyBudget (input : Theorem55.StripInput) : Nat :=
  let space := encodedListSpace (PolyominoStripWindow.Savitch.suffix (rawCells input) input.1 (bound input))
  1000*(space+PolyominoStripWindow.Savitch.cutCoefficient*(space+input.2.length+2)+TranslationStrip.Savitch.searchBudget input.1 (bound input) space+2)

def suffixDecisionBudget (input : Theorem55.StripInput) : Nat :=
  let space := encodedListSpace (PolyominoStripWindow.Savitch.suffix (rawCells input) input.1 (bound input))
  guardBudget space (guardCoefficient*(space+1)) (bodyBudget input)

def decisionBudget (input : Theorem55.StripInput) : Nat :=
  suffixDecisionBudget input+suffixCoefficient*(encodedListSpace (fields input)+1)

theorem decision_eq (input : Theorem55.StripInput) :
    TranslationStrip.decideStripRaw input = (decide (0 < input.1 ∧ input.2 ≠ []) &&
      (PolyominoConnectivitySearch.disconnectedPacked input.2 && TranslationStrip.tilingCheck (rawCells input) input.1 (bound input))) := by
  simp [TranslationStrip.decideStripRaw,Bool.and_assoc]

theorem suffixDecision_eval (input : Theorem55.StripInput) :
    suffixDecisionCode.eval (PolyominoStripWindow.Savitch.suffix (rawCells input) input.1 (bound input)) = pure [(TranslationStrip.decideStripRaw input).toNat] := by
  let values := PolyominoStripWindow.Savitch.suffix (rawCells input) input.1 (bound input)
  have guard : guardExpr.code.eval values = pure [(decide (0 < input.1 ∧ input.2 ≠ [])).toNat] := by
    rw [Expr.code_eval,guard_eval]
  by_cases hg : 0 < input.1 ∧ input.2 ≠ []
  · have cut := PolyominoStripWindow.Savitch.cut_eval (rawCells input) input.1 (bound input) hg.2
    have search := TranslationStrip.Savitch.search_eval (rawCells input) input.1 (bound input) (raw_bounded input)
    let a := PolyominoConnectivitySearch.disconnectedPacked input.2
    let b := TranslationStrip.tilingCheck (rawCells input) input.1 (bound input)
    have both := Code.boolAnd_eval_at PolyominoStripWindow.Savitch.cutCode TranslationStrip.Savitch.searchCode values a.toNat b.toNat cut search
    have both' : bodyCode.eval values = pure [(a && b).toNat] := by
      cases ha : a <;> cases hb : b <;> simpa [bodyCode,ha,hb] using both
    have run := Code.branchZero_eval_succ_at guardExpr.code Code.zero bodyCode values 1
      (by simpa [hg] using guard) [(a && b).toNat] both' (by decide)
    simpa [suffixDecisionCode,decision_eq,hg,a,b,values] using run
  · have run := Code.branchZero_eval_zero_at guardExpr.code Code.zero bodyCode values 0
      (by simpa [hg] using guard) [0] (by simp) rfl
    simpa [suffixDecisionCode,decision_eq,hg,values] using run

theorem decide_eval (input : Theorem55.StripInput) :
    decideCode.eval (fields input) = pure [(TranslationStrip.decideStripRaw input).toNat] := by
  simp [decideCode,suffix_eval,suffixDecision_eval,Part.bind_eq_bind]

theorem suffixDecision_fits (input : Theorem55.StripInput) :
    EvaluatorCodeFits suffixDecisionCode (PolyominoStripWindow.Savitch.suffix (rawCells input) input.1 (bound input))
      [(TranslationStrip.decideStripRaw input).toNat] (suffixDecisionBudget input) := by
  let values := PolyominoStripWindow.Savitch.suffix (rawCells input) input.1 (bound input)
  have guard := guardExpr.code_fits_automatic values guard_noPower
  rw [guard_eval] at guard
  have body : decide (0 < input.1 ∧ input.2 ≠ []) = true → EvaluatorCodeFits bodyCode values
      [(PolyominoConnectivitySearch.disconnectedPacked input.2 && TranslationStrip.tilingCheck (rawCells input) input.1 (bound input)).toNat]
      (bodyBudget input) := by
    intro hg
    have h := of_decide_eq_true hg
    have cut := PolyominoStripWindow.Savitch.cut_fits (rawCells input) input.1 (bound input) h.2
    have search := TranslationStrip.Savitch.search_fits (rawCells input) input.1 (bound input) (raw_bounded input)
    exact boolAnd_bool cut search
  have result := guard_bool guard body
  rw [← decision_eq] at result
  exact result

theorem decide_fits (input : Theorem55.StripInput) :
    EvaluatorCodeFits decideCode (fields input) [(TranslationStrip.decideStripRaw input).toNat] (decisionBudget input) :=
  comp (suffixDecision_fits input) (suffix_fits input)

end LeanTrominoes.TranslationStrip.Evaluator
