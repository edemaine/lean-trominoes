/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarSATIncidenceCounts

/-! # Linear-space incidence count verification on the combined encoding -/
namespace LeanTrominoes.PeriodicPlanarSAT.IncidenceCounts
open FlatEncoding BoundedArithmetic
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits

def variablesCode : Code := PeriodicCNF.IncidenceFields.variableCountCode.comp Code.dynamicDropCode

def variablesCoefficient : Nat := PeriodicCNF.IncidenceFields.variableCountCoefficient*(1000000+1)+1000000

theorem variablesCode_eval (input : Input Nat) :
    variablesCode.eval (fields input) = pure [input.1.variableOccurrences.dedup.length] := by
  simp [variablesCode,formulaProjection_eval,PeriodicCNF.IncidenceFields.variableCountCode_eval,Part.bind_eq_bind]

theorem variablesCode_fits (input : Input Nat) :
    EvaluatorCodeFits variablesCode (fields input) [input.1.variableOccurrences.dedup.length]
      (variablesCoefficient*(encodedListSpace (fields input)+1)) := by
  have count := PeriodicCNF.IncidenceFields.variableCountCode_fits input.1
  rw [← PeriodicCNF.FieldSavitch.fields_space] at count
  have projection := formulaProjection_fits input
  rw [← fields_space] at projection
  exact comp_linear count projection

def inputCode : Code := Code.prepend variablesCode (Code.prepend GridGuard.countCode Code.id)

def inputCoefficient : Nat := 4*(variablesCoefficient+4*(GridGuard.countCoefficient+10+1)+1)

theorem inputCode_eval (input : Input Nat) : inputCode.eval (fields input) = pure (context input) := by
  simp [inputCode,Code.prepend,variablesCode_eval,GridGuard.countCode_eval,context]

theorem inputCode_fits (input : Input Nat) :
    EvaluatorCodeFits inputCode (fields input) (context input)
      (inputCoefficient*(encodedListSpace (fields input)+1)) := by
  have ident := (EvaluatorCodeFits.id (fields input)).mono (idCost_bound _)
  exact prepend_linear (variablesCode_fits input) (prepend_linear (GridGuard.countCode_fits input) ident)

def code : Code := decision.code.comp inputCode

def coefficient : Nat := decision.weight*(decision.radius+1)*(inputCoefficient+1)+inputCoefficient

theorem code_eval (input : Input Nat) : code.eval (fields input) = pure [(result input).toNat] := by
  simp [code,inputCode_eval,Expr.code_eval,decision_eval,Part.bind_eq_bind]

theorem code_fits (input : Input Nat) :
    EvaluatorCodeFits code (fields input) [(result input).toNat]
      (coefficient*((finEncoding.encode input).length+1)) := by
  have guard := decision.code_fits_automatic (context input) decision_noPower
  rw [decision_eval] at guard
  have fit := comp_linear guard (inputCode_fits input)
  rw [fields_space] at fit
  exact fit

noncomputable def spacePolynomial : Polynomial Nat := Polynomial.C coefficient*(Polynomial.X+1)

noncomputable def decider : Complexity.DeciderInPolySpace finEncoding Valid :=
  deciderInPolySpace_of_flatEvaluatorRunFits fields decodeFields decodeFields_fields
    code result (fun _ => by simp [result])
    (fun input => by rw [code_eval]; apply Part.mem_some_iff.mpr; cases result input <;> rfl)
    spacePolynomial (fun input => by
      simp only [spacePolynomial,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
      change EvaluatorRunFits code (fields input) (coefficient*((finEncoding.encode input).length+1))
      let fit := code_fits input
      let after := EvaluatorExecutionFits.ret_halt fit.output_space
      apply EvaluatorRunFits.of_call
      exact fit.call .halt _ (by simp [finEncoding,continuationSpace,trContStack]) after)

theorem valid_inPSPACE : Complexity.InPSPACE finEncoding Valid := ⟨decider⟩

end LeanTrominoes.PeriodicPlanarSAT.IncidenceCounts
