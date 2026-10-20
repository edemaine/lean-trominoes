/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Planar.PeriodicPlanarSATLinePolySpaceMembership
import LeanTrominoes.SAT.Planar.PeriodicPlanarSATGeometricProgram

/-! # Polynomial-space membership with orthogonal, endpoint-separated drawings

All four verifiers read the original flat formula and drawing fields. The
additional geometry program uses signed coordinate residues and stored point
indices, so its endpoint-contact check covers arbitrary representatives.
-/
namespace LeanTrominoes.PeriodicPlanarSAT.GeometricMembership
open ComponentVerification FlatEncoding Turing Turing.ToPartrec Turing.PartrecToTM2
open Turing.PartrecToTM2.EvaluatorCodeFits Polynomial

namespace FormulaVerifier
variable (v : ComponentVerification.FormulaVerifier) (orbit : Bool) (grid : Nat)

def code : Code := Code.boolAnd (v.fullCode orbit grid) GeometricProgram.normalized.code

def result (input : Input Nat) : Bool := v.fullResult orbit grid input && GeometricProgram.result input

noncomputable def space : Polynomial Nat :=
  1000*(X+v.fullSpace orbit grid+C GeometricProgram.normalized.coefficient*(X+1)+2)

theorem code_eval (input : Input Nat) :
    (code v orbit grid).eval (fields input) = pure [(result v orbit grid input).toNat] := by
  have h := Code.boolAnd_eval_at (v.fullCode orbit grid) GeometricProgram.normalized.code (fields input)
    (v.fullResult orbit grid input).toNat (GeometricProgram.result input).toNat
    (v.fullCode_eval orbit grid input) (GeometricProgram.code_eval input)
  cases ha : v.fullResult orbit grid input <;> cases hb : GeometricProgram.result input <;>
    simpa [code,result,ha,hb] using h

theorem code_fits (input : Input Nat) :
    EvaluatorCodeFits (code v orbit grid) (fields input) [(result v orbit grid input).toNat]
      ((space v orbit grid).eval (finEncoding.encode input).length) := by
  have fit := boolAnd_bool (v.fullCode_fits orbit grid input) (GeometricProgram.code_fits input)
  rw [fields_space] at fit
  simpa only [code,result,space,Polynomial.eval_mul,Polynomial.eval_add,
    Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one] using fit

noncomputable def decider {language : Input Nat → Prop}
    (correct : ∀ input, language input ↔ v.precheck orbit grid input=true ∧ input.2.RoutesMatch input.1.incidenceGraph) :
    Complexity.DeciderInPolySpace finEncoding (Geometric language) :=
  deciderInPolySpace_of_flatEvaluatorRunFits fields decodeFields decodeFields_fields
    (code v orbit grid) (result v orbit grid)
    (fun input => by
      rw [result,Bool.and_eq_true,v.fullResult_correct,GeometricProgram.result_correct]
      exact and_congr (correct input).symm Iff.rfl)
    (fun input => by rw [code_eval]; apply Part.mem_some_iff.mpr; cases result v orbit grid input <;> rfl)
    (space v orbit grid) (fun input => by
      let fit := code_fits v orbit grid input
      let after := EvaluatorExecutionFits.ret_halt fit.output_space
      apply EvaluatorRunFits.of_call
      exact fit.call .halt _ (by simp [finEncoding,continuationSpace,trContStack]) after)

end FormulaVerifier

theorem ordinary_inPSPACE : Complexity.InPSPACE finEncoding (Geometric Orbit.LocalOneDimensionalProblem) :=
  ⟨FormulaVerifier.decider ordinary true 8847360 ordinary_iff_precheck_routes⟩

theorem ordinaryThree_inPSPACE : Complexity.InPSPACE finEncoding (Geometric Orbit.LocalOneDimensionalThreeOccurrenceProblem) :=
  ⟨FormulaVerifier.decider ordinaryThree true 8847360 ordinaryThree_iff_precheck_routes⟩

theorem exactOne_inPSPACE : Complexity.InPSPACE finEncoding (Geometric Unbounded.LocalOneDimensionalExactOneProblem) :=
  ⟨FormulaVerifier.decider exactOne false 637009920 exactOne_iff_precheck_routes⟩

theorem exactOneThree_inPSPACE : Complexity.InPSPACE finEncoding (Geometric Unbounded.LocalOneDimensionalExactOneThreeOccurrenceProblem) :=
  ⟨FormulaVerifier.decider exactOneThree false 637009920 exactOneThree_iff_precheck_routes⟩

end LeanTrominoes.PeriodicPlanarSAT.GeometricMembership
