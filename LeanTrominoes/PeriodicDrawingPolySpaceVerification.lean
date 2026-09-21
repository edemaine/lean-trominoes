/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicDrawingArithmeticCorrectness
import LeanTrominoes.PeriodicDrawingFlatEncoding
import LeanTrominoes.PartrecFlatFieldPolySpace

/-! # A compiled linear-space verifier for binary periodic geometry fields

The input consists of period, coordinate radius, segment and vertex counts,
then six fields per indexed segment and two per vertex, followed by the route
trailer needed for lossless decoding. The verifier uses
bounded counters instead of materializing the translation and point lists.
This gives an encoded PSPACE endpoint for the drawing itself. Integrating
formula compatibility and SAT remains a separate compilation obligation.
-/
namespace LeanTrominoes.PeriodicGridDrawing.Arithmetic
open BoundedArithmetic Turing Turing.ToPartrec Turing.PartrecToTM2
open Turing.PartrecToTM2.EvaluatorCodeFits

def coefficient : Nat := decision.weight*(decision.radius+1)

theorem code_eval (d : PeriodicGridDrawing) :
    decision.code.eval (fields d) = pure [(FiniteBounds.check d).toNat] := by
  rw [Expr.code_eval,decision_eval]

theorem code_fits (d : PeriodicGridDrawing) :
    EvaluatorCodeFits decision.code (fields d) [(FiniteBounds.check d).toNat]
      (coefficient*(encodedListSpace (fields d)+1)) := by
  have h := decision_fits (fields d)
  rw [decision_eval] at h
  exact h

theorem run_fits (d : PeriodicGridDrawing) :
    EvaluatorRunFits decision.code (fields d) (coefficient*(encodedListSpace (fields d)+1)) := by
  let fit := code_fits d
  let after := EvaluatorExecutionFits.ret_halt fit.output_space
  apply EvaluatorRunFits.of_call
  exact fit.call .halt _ (by simp [continuationSpace,trContStack]) after

theorem fields_space (d : PeriodicGridDrawing) :
    encodedListSpace (fields d) = (finEncoding.encode d).length := by
  change encodedListSpace (fields d) = (PeriodicCNFFlatEncoding.encodeNatFields (fields d)).length
  rw [PeriodicCNFFlatEncoding.encodeNatFields_length,encodedListSpace_eq_sum]

noncomputable def spacePolynomial : Polynomial Nat := Polynomial.C coefficient*(Polynomial.X+1)

noncomputable def decider : Complexity.DeciderInPolySpace finEncoding IsContinuouslyPlanar :=
  deciderInPolySpace_of_flatEvaluatorRunFits fields decodeFields decodeFields_fields
    decision.code FiniteBounds.check FiniteBounds.check_correct
    (fun d => by rw [code_eval]; apply Part.mem_some_iff.mpr; cases FiniteBounds.check d <;> rfl)
    spacePolynomial (fun d => by
      have fitted := run_fits d
      rw [fields_space] at fitted
      simpa only [spacePolynomial,finEncoding,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_add,
        Polynomial.eval_X,Polynomial.eval_one] using fitted)

theorem isContinuouslyPlanar_inPSPACE : Complexity.InPSPACE finEncoding IsContinuouslyPlanar := ⟨decider⟩

end LeanTrominoes.PeriodicGridDrawing.Arithmetic
