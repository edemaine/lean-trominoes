/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Theorem55StripEvaluatorSpace
import LeanTrominoes.Theorem55StripUnaryPreparation
import LeanTrominoes.PartrecPreparedEvaluatorSpace

/-! # PSPACE membership for the original unary two-tile strip problem -/

noncomputable section
namespace LeanTrominoes.Theorem55StripDecider.Evaluator
open Turing.PartrecToTM2

theorem run_fits_polynomial (input : Theorem55.StripInput) :
    EvaluatorRunFits decideCode (fields input)
      (spacePolynomial.eval (Theorem55StripEncoding.finEncoding.encode input).length) := by
  let fit := decide_fits_polynomial input
  let after := EvaluatorExecutionFits.ret_halt fit.output_space
  apply EvaluatorRunFits.of_call
  exact fit.call .halt _ (by simp [continuationSpace,trContStack]) after

def stripDecider : Complexity.DeciderInPolySpace Theorem55StripEncoding.finEncoding Theorem55.stripProblem :=
  deciderInPolySpace_of_preparedEvaluator Theorem55StripEncoding.finEncoding fields
    (Complexity.FiniteAlphabetComputableInPolyTime.ofComputableInPolyTime nativePreparation_compiler)
    decideCode Theorem55.stripProblem decideStripRaw decideStripRaw_correct
    (fun input => by rw [decide_eval]; apply Part.mem_some_iff.mpr; cases decideStripRaw input <;> rfl)
    spacePolynomial run_fits_polynomial

end LeanTrominoes.Theorem55StripDecider.Evaluator

namespace LeanTrominoes.Theorem55
/-- PSPACE membership uses the exact unary encoding in `stripStatement`. -/
theorem strip_inPSPACE : Complexity.InPSPACE Theorem55StripEncoding.finEncoding stripProblem :=
  ⟨Theorem55StripDecider.Evaluator.stripDecider⟩
end LeanTrominoes.Theorem55
