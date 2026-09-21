/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarSATRouteSemantics
import LeanTrominoes.PeriodicPlanarSATRouteObligation

/-! # Complete native polynomial-space verification of supplied planar inputs -/
namespace LeanTrominoes.PeriodicPlanarSAT.ComponentVerification.FormulaVerifier
open FlatEncoding Turing Turing.ToPartrec Turing.PartrecToTM2
open Turing.PartrecToTM2.EvaluatorCodeFits Polynomial
variable (v : FormulaVerifier) (orbit : Bool) (grid : Nat)

def fullCode : Code := Code.boolAnd (v.precheckCode orbit grid) RouteProgram.code

def fullResult (input : Input Nat) : Bool := v.precheck orbit grid input && RouteProgram.result input

noncomputable def fullSpace : Polynomial Nat :=
  1000*(X+v.precheckSpace orbit grid+C RouteProgram.coefficient*(X+1)+2)

theorem fullCode_eval (input : Input Nat) :
    (v.fullCode orbit grid).eval (fields input) = pure [(v.fullResult orbit grid input).toNat] := by
  have h := Code.boolAnd_eval_at (v.precheckCode orbit grid) RouteProgram.code (fields input)
    (v.precheck orbit grid input).toNat (RouteProgram.result input).toNat
    (v.precheckCode_eval orbit grid input) (RouteProgram.code_eval input)
  cases ha : v.precheck orbit grid input <;> cases hb : RouteProgram.result input <;>
    simpa [fullCode,fullResult,ha,hb] using h

theorem fullCode_fits (input : Input Nat) :
    EvaluatorCodeFits (v.fullCode orbit grid) (fields input) [(v.fullResult orbit grid input).toNat]
      ((v.fullSpace orbit grid).eval (finEncoding.encode input).length) := by
  have fit := boolAnd_bool (v.precheckCode_fits orbit grid input) (RouteProgram.code_fits input)
  rw [fields_space] at fit
  simpa only [fullCode,fullResult,fullSpace,Polynomial.eval_mul,Polynomial.eval_add,
    Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one] using fit

theorem precheck_valid (input : Input Nat) (h : v.precheck orbit grid input=true) : IncidenceCounts.Valid input := by
  simp only [precheck,Bool.and_eq_true] at h
  exact ((VertexVerification.check_correct orbit input).mp h.1).1

theorem fullResult_correct (input : Input Nat) :
    v.fullResult orbit grid input=true ↔
      v.precheck orbit grid input=true ∧ input.2.RoutesMatch input.1.incidenceGraph := by
  rw [fullResult,Bool.and_eq_true]
  constructor
  · rintro ⟨hp,hr⟩
    exact ⟨hp,(RouteProgram.result_correct input (v.precheck_valid orbit grid input hp)).mp hr⟩
  · rintro ⟨hp,hr⟩
    exact ⟨hp,(RouteProgram.result_correct input (v.precheck_valid orbit grid input hp)).mpr hr⟩

noncomputable def fullDecider {language : Input Nat → Prop}
    (correct : ∀ input, language input ↔ v.precheck orbit grid input=true ∧ input.2.RoutesMatch input.1.incidenceGraph) :
    Complexity.DeciderInPolySpace finEncoding language :=
  deciderInPolySpace_of_flatEvaluatorRunFits fields decodeFields decodeFields_fields
    (v.fullCode orbit grid) (v.fullResult orbit grid)
    (fun input => (v.fullResult_correct orbit grid input).trans (correct input).symm)
    (fun input => by rw [v.fullCode_eval]; apply Part.mem_some_iff.mpr; cases v.fullResult orbit grid input <;> rfl)
    (v.fullSpace orbit grid) (fun input => by
      let fit := v.fullCode_fits orbit grid input
      let after := EvaluatorExecutionFits.ret_halt fit.output_space
      apply EvaluatorRunFits.of_call
      exact fit.call .halt _ (by simp [finEncoding,continuationSpace,trContStack]) after)

end LeanTrominoes.PeriodicPlanarSAT.ComponentVerification.FormulaVerifier
