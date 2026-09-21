/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicExactOneFieldEvaluator
import LeanTrominoes.PartrecFlatFieldPolySpace

/-! # Native flat-encoded PSPACE membership for local one-dimensional 1-in-3SAT -/
namespace LeanTrominoes.PeriodicCNF.ExactOneFieldSavitch
open PeriodicCNFFlatEncoding Turing.PartrecToTM2

theorem run_fits (f : PeriodicCNF Nat) :
    EvaluatorRunFits decideCode (formulaFields f)
      (spacePolynomial.eval (finEncoding.encode f).length) := by
  let fit := decide_fits f
  let after := EvaluatorExecutionFits.ret_halt fit.output_space
  apply EvaluatorRunFits.of_call
  exact fit.call .halt _ (by simp [continuationSpace,trContStack]) after

noncomputable def decider : Complexity.DeciderInPolySpace finEncoding
    PeriodicExactOneCNF.LocalOneDimensionalThreeSAT :=
  deciderInPolySpace_of_flatEvaluatorRunFits formulaFields decodeFormulaFields decodeFormulaFields_formulaFields
    decideCode result result_correct
    (fun f => by rw [decide_eval]; apply Part.mem_some_iff.mpr; cases result f <;> rfl)
    spacePolynomial run_fits
end LeanTrominoes.PeriodicCNF.ExactOneFieldSavitch
namespace LeanTrominoes.PeriodicExactOneCNF

theorem localOneDimensionalThreeSAT_inPSPACE :
    Complexity.InPSPACE PeriodicCNFFlatEncoding.finEncoding LocalOneDimensionalThreeSAT :=
  ⟨PeriodicCNF.ExactOneFieldSavitch.decider⟩
end LeanTrominoes.PeriodicExactOneCNF
