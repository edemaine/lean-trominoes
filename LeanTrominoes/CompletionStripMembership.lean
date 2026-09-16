/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionStripEvaluatorSpace
import LeanTrominoes.CompletionStripPreparation
import LeanTrominoes.PartrecPreparedEvaluatorSpace

/-! # PSPACE membership for periodic strip tromino completion

The encoding writes the strip height, period, and preplaced motif fields
in unary. Invalid prefills, including overlaps between periodic copies,
are rejected before the uncovered strip is compiled.
-/
noncomputable section
namespace LeanTrominoes.PeriodicStripTrominoPrefill.Raw.Evaluator
open Turing.PartrecToTM2

theorem run_fits (t : Tromino) (input : PeriodicStripTrominoPrefill) :
    EvaluatorRunFits (decideCode t) (fields input)
      ((spacePolynomial t).eval (CompletionStripEncoding.finEncoding.encode input).length) := by
  let fit := decide_fits t input
  let after := EvaluatorExecutionFits.ret_halt fit.output_space
  apply EvaluatorRunFits.of_call
  exact fit.call .halt _ (by simp [continuationSpace,trContStack]) after

def stripDecider (t : Tromino) :
    Complexity.DeciderInPolySpace CompletionStripEncoding.finEncoding (problem t) :=
  deciderInPolySpace_of_preparedEvaluator CompletionStripEncoding.finEncoding fields
    (Complexity.FiniteAlphabetComputableInPolyTime.ofComputableInPolyTime Preparation.nativePreparation_compiler)
    (decideCode t) (problem t) (result t) (result_correct t)
    (fun input => by rw [decide_eval]; apply Part.mem_some_iff.mpr; cases result t input <;> rfl)
    (spacePolynomial t) (run_fits t)

end LeanTrominoes.PeriodicStripTrominoPrefill.Raw.Evaluator
namespace LeanTrominoes.PeriodicStripTrominoPrefill

/-- Both L- and I-tromino strip completion are in PSPACE under the explicit unary encoding. -/
theorem problem_inPSPACE (t : Tromino) :
    Complexity.InPSPACE CompletionStripEncoding.finEncoding (problem t) :=
  ⟨Raw.Evaluator.stripDecider t⟩

end LeanTrominoes.PeriodicStripTrominoPrefill
