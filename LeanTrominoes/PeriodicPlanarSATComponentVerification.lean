/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarSATFlatEncoding
import LeanTrominoes.BoundedArithmeticSlice
import LeanTrominoes.PeriodicDrawingPolySpaceVerification
import LeanTrominoes.PartrecBooleanUniformSpace

/-! # Formula and drawing verification on a single native input

This composition checks a supplied formula predicate and continuous planarity
of the supplied drawing. Incidence compatibility is deliberately a separate
obligation: planarity alone does not certify a drawing of the formula.
-/
namespace LeanTrominoes.PeriodicPlanarSAT.ComponentVerification
open FlatEncoding BoundedArithmetic Turing Turing.ToPartrec Turing.PartrecToTM2
open Turing.PartrecToTM2.EvaluatorCodeFits Polynomial

def drawingDecision : Expr := PeriodicGridDrawing.Arithmetic.decision.slice 0

def drawingCoefficient : Nat := drawingDecision.weight*(drawingDecision.radius+1)

theorem drawingDecision_eval (input : Input Nat) :
    drawingDecision.eval (fields input) = (PeriodicGridDrawing.FiniteBounds.check input.2).toNat := by
  have h := Expr.slice_eval PeriodicGridDrawing.Arithmetic.decision []
    (drawingFields input.2) (PeriodicCNFFlatEncoding.formulaFields input.1)
  simpa only [drawingDecision,fields,List.length_nil,List.nil_append,PeriodicGridDrawing.Arithmetic.decision_eval] using h

theorem drawingCode_eval (input : Input Nat) :
    drawingDecision.code.eval (fields input) = pure [(PeriodicGridDrawing.FiniteBounds.check input.2).toNat] := by
  rw [Expr.code_eval,drawingDecision_eval]

theorem drawingCode_fits (input : Input Nat) :
    EvaluatorCodeFits drawingDecision.code (fields input)
      [(PeriodicGridDrawing.FiniteBounds.check input.2).toNat]
      (drawingCoefficient*((finEncoding.encode input).length+1)) := by
  have allowed : drawingDecision.noPower = true := by
    rw [drawingDecision,Expr.slice_noPower]
    exact PeriodicGridDrawing.Arithmetic.decision_noPower
  have fit := drawingDecision.code_fits_automatic (fields input) allowed
  rw [drawingDecision_eval,fields_space] at fit
  exact fit

private theorem eval_mono (p : Polynomial Nat) {a b : Nat} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using Nat.add_le_add hp hq
  | monomial n c => simpa only [Polynomial.eval_monomial] using Nat.mul_le_mul_left c (Nat.pow_le_pow_left h n)

/-- A formula program together with its native field semantics and space bound. -/
structure FormulaVerifier where
  code : Code
  result : PeriodicCNF Nat → Bool
  space : Polynomial Nat
  evaluates : ∀ f, code.eval (PeriodicCNFFlatEncoding.formulaFields f) = pure [(result f).toNat]
  fits : ∀ f, EvaluatorCodeFits code (PeriodicCNFFlatEncoding.formulaFields f) [(result f).toNat]
    (space.eval (PeriodicCNFFlatEncoding.finEncoding.encode f).length)

namespace FormulaVerifier
variable (v : FormulaVerifier)

def formulaCode : Code := v.code.comp Code.dynamicDropCode

noncomputable def formulaSpace : Polynomial Nat := v.space + C 1000000*(X+1)

theorem formulaCode_eval (input : Input Nat) :
    v.formulaCode.eval (fields input) = pure [(v.result input.1).toNat] := by
  simp [formulaCode,formulaProjection_eval,v.evaluates,Part.bind_eq_bind]

theorem formulaCode_fits (input : Input Nat) :
    EvaluatorCodeFits v.formulaCode (fields input) [(v.result input.1).toNat]
      (v.formulaSpace.eval (finEncoding.encode input).length) := by
  have fit := EvaluatorCodeFits.comp (v.fits input.1) (formulaProjection_fits input)
  apply fit.mono
  have h := eval_mono v.space (formula_space_le input)
  simp only [formulaSpace,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_X,Polynomial.eval_one]
  omega

def combinedCode : Code := Code.boolAnd drawingDecision.code v.formulaCode

def combinedResult (input : Input Nat) : Bool :=
  PeriodicGridDrawing.FiniteBounds.check input.2 && v.result input.1

noncomputable def combinedSpace : Polynomial Nat :=
  1000*(X+C drawingCoefficient*(X+1)+v.formulaSpace+2)

theorem code_eval (input : Input Nat) :
    v.combinedCode.eval (fields input) = pure [(v.combinedResult input).toNat] := by
  have h := Code.boolAnd_eval_at drawingDecision.code v.formulaCode (fields input)
    (PeriodicGridDrawing.FiniteBounds.check input.2).toNat (v.result input.1).toNat
    (drawingCode_eval input) (v.formulaCode_eval input)
  cases ha : PeriodicGridDrawing.FiniteBounds.check input.2 <;>
    cases hb : v.result input.1 <;> simpa [combinedCode,combinedResult,ha,hb] using h

theorem code_fits (input : Input Nat) :
    EvaluatorCodeFits v.combinedCode (fields input) [(v.combinedResult input).toNat]
      (v.combinedSpace.eval (finEncoding.encode input).length) := by
  have fit := boolAnd_bool (drawingCode_fits input) (v.formulaCode_fits input)
  rw [fields_space] at fit
  simpa only [combinedCode,combinedResult,combinedSpace,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_C,
    Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one] using fit

theorem combinedResult_correct {language : PeriodicCNF Nat → Prop}
    (correct : ∀ f, v.result f = true ↔ language f) (input : Input Nat) :
    v.combinedResult input = true ↔ language input.1 ∧ input.2.IsContinuouslyPlanar := by
  simp only [combinedResult,Bool.and_eq_true,PeriodicGridDrawing.FiniteBounds.check_correct,correct]
  exact and_comm

theorem run_fits (input : Input Nat) :
    EvaluatorRunFits v.combinedCode (fields input)
      (v.combinedSpace.eval (finEncoding.encode input).length) := by
  let fit := v.code_fits input
  let after := EvaluatorExecutionFits.ret_halt fit.output_space
  apply EvaluatorRunFits.of_call
  exact fit.call .halt _ (by simp [continuationSpace,trContStack]) after

noncomputable def decider {language : PeriodicCNF Nat → Prop}
    (correct : ∀ f, v.result f = true ↔ language f) :
    Complexity.DeciderInPolySpace finEncoding
      (fun input => language input.1 ∧ input.2.IsContinuouslyPlanar) :=
  deciderInPolySpace_of_flatEvaluatorRunFits fields decodeFields decodeFields_fields
    v.combinedCode v.combinedResult (v.combinedResult_correct correct)
    (fun input => by rw [v.code_eval]; apply Part.mem_some_iff.mpr; cases v.combinedResult input <;> rfl)
    v.combinedSpace v.run_fits

end FormulaVerifier
end LeanTrominoes.PeriodicPlanarSAT.ComponentVerification
