/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarSATGridGuard
import LeanTrominoes.PeriodicPlanarSATLineComponentVerification

/-! # Space-certified SAT, planarity, and intrinsic grid bounds

Only the formula/drawing incidence-compatibility guard remains to turn these
component verifiers into the full supplied-drawing language deciders.
-/
namespace LeanTrominoes.PeriodicPlanarSAT.ComponentVerification.FormulaVerifier
open FlatEncoding Turing Turing.ToPartrec Turing.PartrecToTM2
open Turing.PartrecToTM2.EvaluatorCodeFits Polynomial
variable (v : FormulaVerifier) (coefficient : Nat)

def boundedCode : Code := Code.boolAnd (GridGuard.code coefficient) v.combinedCode

def boundedResult (input : Input Nat) : Bool :=
  GridGuard.result coefficient input && v.combinedResult input

noncomputable def boundedSpace : Polynomial Nat :=
  1000*(X+C (GridGuard.codeCoefficient coefficient)*(X+1)+v.combinedSpace+2)

theorem boundedCode_eval (input : Input Nat) :
    (v.boundedCode coefficient).eval (fields input) = pure [(v.boundedResult coefficient input).toNat] := by
  have h := Code.boolAnd_eval_at (GridGuard.code coefficient) v.combinedCode (fields input)
    (GridGuard.result coefficient input).toNat (v.combinedResult input).toNat
    (GridGuard.code_eval coefficient input) (v.code_eval input)
  cases ha : GridGuard.result coefficient input <;> cases hb : v.combinedResult input <;>
    simpa [boundedCode,boundedResult,ha,hb] using h

theorem boundedCode_fits (input : Input Nat) :
    EvaluatorCodeFits (v.boundedCode coefficient) (fields input) [(v.boundedResult coefficient input).toNat]
      ((v.boundedSpace coefficient).eval (finEncoding.encode input).length) := by
  have fit := boolAnd_bool (GridGuard.code_fits coefficient input) (v.code_fits input)
  rw [fields_space] at fit
  simpa only [boundedSpace,boundedCode,boundedResult,Polynomial.eval_mul,Polynomial.eval_add,
    Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one] using fit

theorem boundedResult_correct {language : PeriodicCNF Nat → Prop}
    (correct : ∀ f, v.result f = true ↔ language f) (input : Input Nat) :
    v.boundedResult coefficient input = true ↔
      GridBound coefficient input ∧ language input.1 ∧ input.2.IsContinuouslyPlanar := by
  simp only [boundedResult,Bool.and_eq_true,v.combinedResult_correct correct,
    GridGuard.result,decide_eq_true_eq,GridBound]

noncomputable def boundedDecider {language : PeriodicCNF Nat → Prop}
    (correct : ∀ f, v.result f = true ↔ language f) :
    Complexity.DeciderInPolySpace finEncoding
      (fun input => GridBound coefficient input ∧ language input.1 ∧ input.2.IsContinuouslyPlanar) :=
  deciderInPolySpace_of_flatEvaluatorRunFits fields decodeFields decodeFields_fields
    (v.boundedCode coefficient) (v.boundedResult coefficient) (v.boundedResult_correct coefficient correct)
    (fun input => by rw [v.boundedCode_eval]; apply Part.mem_some_iff.mpr; cases v.boundedResult coefficient input <;> rfl)
    (v.boundedSpace coefficient) (fun input => by
      let fit := v.boundedCode_fits coefficient input
      let after := EvaluatorExecutionFits.ret_halt fit.output_space
      apply EvaluatorRunFits.of_call
      exact fit.call .halt _ (by simp [finEncoding,continuationSpace,trContStack]) after)

end LeanTrominoes.PeriodicPlanarSAT.ComponentVerification.FormulaVerifier

namespace LeanTrominoes.PeriodicPlanarSAT.ComponentVerification
open PeriodicCNF

theorem boundedOrdinary_inPSPACE : Complexity.InPSPACE FlatEncoding.finEncoding
    (fun input => GridBound 8847360 input ∧ LocalPeriodicThreeCNF1DSAT input.1 ∧ input.2.IsContinuouslyPlanar) :=
  ⟨ordinary.boundedDecider 8847360 FieldWidth.result_correct⟩

theorem boundedOrdinaryThree_inPSPACE : Complexity.InPSPACE FlatEncoding.finEncoding
    (fun input => GridBound 8847360 input ∧ LocalPeriodicThreeSATThree1DSAT input.1 ∧ input.2.IsContinuouslyPlanar) :=
  ⟨ordinaryThree.boundedDecider 8847360 FieldOccurrences.result_correct⟩

theorem boundedExactOne_inPSPACE : Complexity.InPSPACE FlatEncoding.finEncoding
    (fun input => GridBound 637009920 input ∧ PeriodicExactOneCNF.LocalOneDimensionalThreeSAT input.1 ∧ input.2.IsContinuouslyPlanar) :=
  ⟨exactOne.boundedDecider 637009920 ExactOneFieldSavitch.result_correct⟩

theorem boundedExactOneThree_inPSPACE : Complexity.InPSPACE FlatEncoding.finEncoding
    (fun input => GridBound 637009920 input ∧ PeriodicExactOneCNF.LocalOneDimensionalThreeSATThree input.1 ∧ input.2.IsContinuouslyPlanar) :=
  ⟨exactOneThree.boundedDecider 637009920 ExactOneFieldOccurrences.result_correct⟩

theorem ordinary_iff_components (input : Input Nat) :
    Orbit.LocalOneDimensionalProblem input ↔
      ordinary.boundedResult 8847360 input = true ∧
        PeriodicGridDrawing.OrbitCertificate.Compatible input.1.incidenceGraph input.2 := by
  rw [ordinary.boundedResult_correct 8847360 FieldWidth.result_correct]
  simp only [Orbit.LocalOneDimensionalProblem,Orbit.BoundedLocalProblem,Orbit.LocalProblem,
    Orbit.Problem,Orbit.Valid,LocalPeriodicThreeCNF1DSAT,← LineWindow.check_localPeriodicCNF1DSAT,LineWindow.check_correct]
  tauto

theorem ordinaryThree_iff_components (input : Input Nat) :
    Orbit.LocalOneDimensionalThreeOccurrenceProblem input ↔
      ordinaryThree.boundedResult 8847360 input = true ∧
        PeriodicGridDrawing.OrbitCertificate.Compatible input.1.incidenceGraph input.2 := by
  rw [ordinaryThree.boundedResult_correct 8847360 FieldOccurrences.result_correct]
  simp only [Orbit.LocalOneDimensionalThreeOccurrenceProblem,Orbit.BoundedLocalThreeOccurrenceProblem,
    Orbit.LocalThreeOccurrenceProblem,Orbit.ThreeOccurrenceProblem,Orbit.Problem,Orbit.Valid,
    LocalPeriodicThreeSATThree1DSAT,LocalPeriodicThreeCNF1DSAT,← LineWindow.check_localPeriodicCNF1DSAT,LineWindow.check_correct]
  tauto

theorem exactOne_iff_components (input : Input Nat) :
    Unbounded.LocalOneDimensionalExactOneProblem input ↔
      exactOne.boundedResult 637009920 input = true ∧
        PeriodicGridDrawing.FiniteCertificate.Compatible input.1.incidenceGraph input.2 := by
  rw [exactOne.boundedResult_correct 637009920 ExactOneFieldSavitch.result_correct]
  simp only [Unbounded.LocalOneDimensionalExactOneProblem,Unbounded.BoundedLocalExactOneProblem,
    Unbounded.LocalExactOneProblem,Unbounded.ExactOneProblem,Unbounded.Valid,
    PeriodicExactOneCNF.LocalOneDimensionalThreeSAT,PeriodicExactOneCNF.LocalOneDimensionalSAT]
  tauto

theorem exactOneThree_iff_components (input : Input Nat) :
    Unbounded.LocalOneDimensionalExactOneThreeOccurrenceProblem input ↔
      exactOneThree.boundedResult 637009920 input = true ∧
        PeriodicGridDrawing.FiniteCertificate.Compatible input.1.incidenceGraph input.2 := by
  rw [exactOneThree.boundedResult_correct 637009920 ExactOneFieldOccurrences.result_correct]
  simp only [Unbounded.LocalOneDimensionalExactOneThreeOccurrenceProblem,
    Unbounded.BoundedLocalExactOneThreeOccurrenceProblem,Unbounded.LocalExactOneThreeOccurrenceProblem,
    Unbounded.ExactOneThreeOccurrenceProblem,Unbounded.ExactOneProblem,Unbounded.Valid,
    PeriodicExactOneCNF.LocalOneDimensionalThreeSATThree,PeriodicExactOneCNF.LocalOneDimensionalThreeSAT,
    PeriodicExactOneCNF.LocalOneDimensionalSAT]
  tauto

end LeanTrominoes.PeriodicPlanarSAT.ComponentVerification
