/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFFieldEvaluator
import LeanTrominoes.PartrecFlatFieldPolySpace
import LeanTrominoes.PeriodicCNFPolySpaceHardness

/-! # PSPACE-completeness of local one-dimensional periodic CNF SAT -/
namespace LeanTrominoes.PeriodicCNF.FieldSavitch
open PeriodicCNFFlatEncoding Turing.PartrecToTM2

theorem run_fits (f : PeriodicCNF Nat) :
    EvaluatorRunFits decideCode (formulaFields f)
      (spacePolynomial.eval (finEncoding.encode f).length) := by
  let fit := decide_fits f
  let after := EvaluatorExecutionFits.ret_halt fit.output_space
  apply EvaluatorRunFits.of_call
  exact fit.call .halt _ (by simp [continuationSpace,trContStack]) after

noncomputable def decider : Complexity.DeciderInPolySpace finEncoding LocalPeriodicCNF1DSAT := by
  exact deciderInPolySpace_of_flatEvaluatorRunFits formulaFields decodeFormulaFields decodeFormulaFields_formulaFields
    decideCode result result_correct
    (fun f => by rw [decide_eval]; apply Part.mem_some_iff.mpr; cases result f <;> rfl)
    spacePolynomial run_fits

end LeanTrominoes.PeriodicCNF.FieldSavitch
namespace LeanTrominoes.PeriodicCNF.PolySpaceHardness

theorem localPeriodicCNF1DSAT_inPSPACE :
    Complexity.InPSPACE PeriodicCNFFlatEncoding.finEncoding LocalPeriodicCNF1DSAT := ⟨FieldSavitch.decider⟩

theorem localPeriodicCNF1DSAT_PSPACEComplete :
    Complexity.PSPACEComplete PeriodicCNFFlatEncoding.finEncoding LocalPeriodicCNF1DSAT :=
  ⟨localPeriodicCNF1DSAT_inPSPACE,localPeriodicCNF1DSAT_PSPACEHard⟩

end LeanTrominoes.PeriodicCNF.PolySpaceHardness
