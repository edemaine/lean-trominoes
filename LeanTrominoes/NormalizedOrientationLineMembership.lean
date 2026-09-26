/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.NormalizedOrientationGuard
import LeanTrominoes.NormalizedOrientationCompletionCompiler
import LeanTrominoes.NormalizedOrientationLineHardness
import LeanTrominoes.PreparedGuardedEvaluator

/-! # Native PSPACE completeness of normalized one-dimensional orientation -/
noncomputable section
namespace LeanTrominoes.Gadget.NormalizedOrientation
open Turing Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits Polynomial
open SafePreparation

private theorem eval_mono (p : Polynomial Nat) {a b : Nat} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using Nat.add_le_add hp hq
  | monomial n c => simpa only [Polynomial.eval_monomial] using Nat.mul_le_mul_left c (Nat.pow_le_pow_left h n)

def completionSpace : Polynomial Nat :=
  (PeriodicStripTrominoPrefill.Raw.Evaluator.spacePolynomial .I).comp
    (TM2OutputLength.outputLengthPolynomial completionCompiler)

theorem completion_fits (d : PeriodicOrthogonalDrawing) :
    EvaluatorCodeFits (PeriodicStripTrominoPrefill.Raw.Evaluator.decideCode .I)
      (PeriodicStripTrominoPrefill.Raw.fields (completion d))
      [(PeriodicStripTrominoPrefill.Raw.Evaluator.result .I (completion d)).toNat]
      (completionSpace.eval (FlatEncoding.finEncoding.encode d).length) := by
  have fit := PeriodicStripTrominoPrefill.Raw.Evaluator.decide_fits .I (completion d)
  apply fit.mono
  rw [completionSpace,Polynomial.eval_comp]
  exact eval_mono _ (TM2OutputLength.output_length_le_polynomial_eval completionCompiler d)

theorem lineResult_correct (d : PeriodicOrthogonalDrawing) :
    (Guard.result d && PeriodicStripTrominoPrefill.Raw.Evaluator.result .I (completion d)) = true ↔ LineProblem d := by
  rw [Bool.and_eq_true,Guard.result_correct,PeriodicStripTrominoPrefill.Raw.Evaluator.result_correct]
  constructor
  · rintro ⟨⟨wf,separated,blank⟩,tiles⟩
    exact ⟨separated,blank,(completion_correct d wf blank).mp tiles⟩
  · rintro ⟨separated,blank,orientation⟩
    exact ⟨⟨orientation.1,separated,blank⟩,(completion_correct d orientation.1 blank).mpr orientation⟩

def lineDecider : Complexity.DeciderInPolySpace FlatEncoding.finEncoding LineProblem := by
  letI : Inhabited FlatEncoding.finEncoding.Γ := ⟨.bit0⟩
  exact PreparedGuardedEvaluator.decider FlatEncoding.finEncoding GuardExpressions.context
    (fun d => PeriodicStripTrominoPrefill.Raw.fields (completion d))
    (BinaryFieldCountPreparation.compiler FlatEncoding.fields) completionFieldsCompiler Guard.decision Guard.result Guard.decision_eval Guard.decision_noPower
    (PeriodicStripTrominoPrefill.Raw.Evaluator.decideCode .I)
    (fun d => PeriodicStripTrominoPrefill.Raw.Evaluator.result .I (completion d))
    (fun d => PeriodicStripTrominoPrefill.Raw.Evaluator.decide_eval .I (completion d))
    completionSpace completion_fits LineProblem lineResult_correct

theorem lineProblem_inPSPACE : Complexity.InPSPACE FlatEncoding.finEncoding LineProblem := ⟨lineDecider⟩

theorem lineProblem_PSPACEComplete : Complexity.PSPACEComplete FlatEncoding.finEncoding LineProblem :=
  ⟨lineProblem_inPSPACE,lineProblem_PSPACEHard⟩

end LeanTrominoes.Gadget.NormalizedOrientation
end
