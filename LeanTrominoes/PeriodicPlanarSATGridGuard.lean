/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarSATComponentVerification
import LeanTrominoes.PeriodicCNFFlatFieldCountSpace
import LeanTrominoes.PeriodicCNFFlatEncodingSize

/-! # Compiling the intrinsic drawing-grid bound on combined inputs -/
namespace LeanTrominoes.PeriodicPlanarSAT.GridGuard
open FlatEncoding BoundedArithmetic BoundedArithmetic.Expr
open PeriodicCNF.FlatScanner Turing Turing.ToPartrec Turing.PartrecToTM2
open Turing.PartrecToTM2.EvaluatorCodeFits

-- Context: formula field count, drawing field count, drawing, formula.
def clauseCount : Expr := .load (var 1+2)
def sizeExpr : Expr := clauseCount+(var 0-1-clauseCount)/4
def decision (coefficient : Nat) : Expr :=
  .ite (leE (var 2) (.literal coefficient*(sizeExpr+1))) 1 0

def context (input : Input Nat) : List Nat :=
  (PeriodicCNFFlatEncoding.formulaFields input.1).length :: fields input

private theorem clauseCount_eval (input : Input Nat) :
    clauseCount.eval (context input) = input.1.clauses.length := by
  simp only [clauseCount,Expr.eval,eval_var,Op.eval,context,fields,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some]
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp [PeriodicCNFFlatEncoding.formulaFields]

private theorem period_eval (input : Input Nat) :
    (var 2).eval (context input) = input.2.gridSize := by
  simp only [eval_var,context,fields,List.getElem?_cons_succ]
  have h : (drawingFields input.2)[0]? = some input.2.gridSize := rfl
  rw [List.getElem?_append_left (show 0 < (drawingFields input.2).length from by
    simp [drawingFields,PeriodicGridDrawing.Arithmetic.fields]),h]
  rfl

theorem sizeExpr_eval (input : Input Nat) : sizeExpr.eval (context input) = input.1.presentationSize := by
  have count : PeriodicCNFFlatEncoding.literalCount input.1 = input.1.presentationLiteralCount := by
    simp [PeriodicCNFFlatEncoding.literalCount,PeriodicCNF.presentationLiteralCount,List.length_flatten]
  change clauseCount.eval (context input) +
    (((var 0).eval (context input)-1-clauseCount.eval (context input))/4) = _
  rw [clauseCount_eval]
  change input.1.clauses.length +
    (((PeriodicCNFFlatEncoding.formulaFields input.1).length-1-input.1.clauses.length)/4) = _
  rw [PeriodicCNFFlatEncoding.formulaFields_length,count]
  unfold PeriodicCNF.presentationSize
  omega

def result (coefficient : Nat) (input : Input Nat) : Bool :=
  decide (input.2.gridSize ≤ coefficient*(input.1.presentationSize+1))

theorem decision_eval (coefficient : Nat) (input : Input Nat) :
    (decision coefficient).eval (context input) = (result coefficient input).toNat := by
  have h : (leE (var 2) (.literal coefficient*(sizeExpr+1))).Truth (context input) ↔
      input.2.gridSize ≤ coefficient*(input.1.presentationSize+1) := by
    rw [truth_le]
    simp only [period_eval,Expr.eval,Op.eval,sizeExpr_eval]
  unfold Truth at h
  simp only [decision,Expr.eval]
  by_cases test : (leE (var 2) (.literal coefficient*(sizeExpr+1))).eval (context input)=0
  · have rejected : ¬input.2.gridSize ≤ coefficient*(input.1.presentationSize+1) := by
      intro yes
      exact h.mpr yes test
    simp [test,result,rejected]
  · simp [test,result,h.mp test]

theorem decision_noPower (coefficient : Nat) : (decision coefficient).noPower = true := by
  simp [decision,sizeExpr,clauseCount,leE,notE,eqE,ltE,Expr.noPower,var]

def countCode : Code := fieldCountCode.comp Code.dynamicDropCode

def countCoefficient : Nat := fieldCountWeight*(1000000+1)+1000000

theorem countCode_eval (input : Input Nat) :
    countCode.eval (fields input) = pure [(PeriodicCNFFlatEncoding.formulaFields input.1).length] := by
  simp [countCode,formulaProjection_eval,fieldCountCode_eval,Part.bind_eq_bind]

theorem countCode_fits (input : Input Nat) :
    EvaluatorCodeFits countCode (fields input) [(PeriodicCNFFlatEncoding.formulaFields input.1).length]
      (countCoefficient*(encodedListSpace (fields input)+1)) := by
  have fit := formulaProjection_fits input
  rw [← fields_space] at fit
  exact comp_linear (fieldCountCode_fits input.1) fit

def code (coefficient : Nat) : Code :=
  (decision coefficient).code.comp (Code.prepend countCode Code.id)

def codeCoefficient (coefficient : Nat) : Nat :=
  ((decision coefficient).weight*((decision coefficient).radius+1))*(4*(countCoefficient+10+1)+1)+4*(countCoefficient+10+1)

theorem code_eval (coefficient : Nat) (input : Input Nat) :
    (code coefficient).eval (fields input) = pure [(result coefficient input).toNat] := by
  have init : (Code.prepend countCode Code.id).eval (fields input) = pure (context input) := by
    simp [Code.prepend,countCode_eval,context]
  simp [code,init,Expr.code_eval,decision_eval,Part.bind_eq_bind]

theorem code_fits (coefficient : Nat) (input : Input Nat) :
    EvaluatorCodeFits (code coefficient) (fields input) [(result coefficient input).toNat]
      (codeCoefficient coefficient*((finEncoding.encode input).length+1)) := by
  have ident := (EvaluatorCodeFits.id (fields input)).mono (idCost_bound (fields input))
  have init := prepend_linear (countCode_fits input) ident
  have guard := (decision coefficient).code_fits_automatic (context input) (decision_noPower coefficient)
  rw [decision_eval] at guard
  have fit := comp_linear guard init
  rw [fields_space] at fit
  exact fit

end LeanTrominoes.PeriodicPlanarSAT.GridGuard
