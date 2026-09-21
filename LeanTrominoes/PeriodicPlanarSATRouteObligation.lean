/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarSATVertexVerification
import LeanTrominoes.PeriodicPlanarSATBoundedComponentVerification

/-! # The remaining route-endpoint obligation for planar 1D SAT

All other supplied-input conditions now have a single compiled verifier with
a polynomial space bound. These equivalences identify the missing condition
without assuming that an unrelated planar drawing represents the formula.
-/
namespace LeanTrominoes.PeriodicPlanarSAT.ComponentVerification.FormulaVerifier
open FlatEncoding Turing Turing.ToPartrec Turing.PartrecToTM2
open Turing.PartrecToTM2.EvaluatorCodeFits Polynomial
variable (v : FormulaVerifier) (orbit : Bool) (grid : Nat)

def precheckCode : Code := Code.boolAnd (VertexVerification.code orbit) (v.boundedCode grid)

def precheck (input : Input Nat) : Bool := VertexVerification.check orbit input && v.boundedResult grid input

noncomputable def precheckSpace : Polynomial Nat :=
  1000*(X+C (VertexVerification.coefficient orbit)*(X+1)+v.boundedSpace grid+2)

theorem precheckCode_eval (input : Input Nat) :
    (v.precheckCode orbit grid).eval (fields input) = pure [(v.precheck orbit grid input).toNat] := by
  have h := Code.boolAnd_eval_at (VertexVerification.code orbit) (v.boundedCode grid) (fields input)
    (VertexVerification.check orbit input).toNat (v.boundedResult grid input).toNat
    (VertexVerification.code_eval orbit input) (v.boundedCode_eval grid input)
  cases ha : VertexVerification.check orbit input <;> cases hb : v.boundedResult grid input <;>
    simpa [precheckCode,precheck,ha,hb] using h

theorem precheckCode_fits (input : Input Nat) :
    EvaluatorCodeFits (v.precheckCode orbit grid) (fields input) [(v.precheck orbit grid input).toNat]
      ((v.precheckSpace orbit grid).eval (finEncoding.encode input).length) := by
  have fit := boolAnd_bool (VertexVerification.code_fits orbit input) (v.boundedCode_fits grid input)
  rw [fields_space] at fit
  simpa only [precheckCode,precheck,precheckSpace,Polynomial.eval_mul,Polynomial.eval_add,
    Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one] using fit

end LeanTrominoes.PeriodicPlanarSAT.ComponentVerification.FormulaVerifier

namespace LeanTrominoes.PeriodicPlanarSAT.ComponentVerification

theorem ordinary_iff_precheck_routes (input : Input Nat) :
    Orbit.LocalOneDimensionalProblem input ↔
      ordinary.precheck true 8847360 input = true ∧ input.2.RoutesMatch input.1.incidenceGraph := by
  rw [ordinary_iff_components,VertexVerification.orbit_compatible_iff]
  simp only [FormulaVerifier.precheck,Bool.and_eq_true]
  tauto

theorem ordinaryThree_iff_precheck_routes (input : Input Nat) :
    Orbit.LocalOneDimensionalThreeOccurrenceProblem input ↔
      ordinaryThree.precheck true 8847360 input = true ∧ input.2.RoutesMatch input.1.incidenceGraph := by
  rw [ordinaryThree_iff_components,VertexVerification.orbit_compatible_iff]
  simp only [FormulaVerifier.precheck,Bool.and_eq_true]
  tauto

theorem exactOne_iff_precheck_routes (input : Input Nat) :
    Unbounded.LocalOneDimensionalExactOneProblem input ↔
      exactOne.precheck false 637009920 input = true ∧ input.2.RoutesMatch input.1.incidenceGraph := by
  rw [exactOne_iff_components,VertexVerification.finite_compatible_iff]
  simp only [FormulaVerifier.precheck,Bool.and_eq_true]
  tauto

theorem exactOneThree_iff_precheck_routes (input : Input Nat) :
    Unbounded.LocalOneDimensionalExactOneThreeOccurrenceProblem input ↔
      exactOneThree.precheck false 637009920 input = true ∧ input.2.RoutesMatch input.1.incidenceGraph := by
  rw [exactOneThree_iff_components,VertexVerification.finite_compatible_iff]
  simp only [FormulaVerifier.precheck,Bool.and_eq_true]
  tauto

end LeanTrominoes.PeriodicPlanarSAT.ComponentVerification
