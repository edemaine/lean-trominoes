/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarSATFlatEncoding
import LeanTrominoes.PeriodicCNFFieldEvaluator
import LeanTrominoes.NativeScalarAdapters

/-! # A shared formula/drawing environment for endpoint queries -/
namespace LeanTrominoes.PeriodicPlanarSAT.RouteInput
open FlatEncoding PeriodicCNFFlatEncoding PeriodicCNF.FlatScanner
open BoundedArithmetic BoundedArithmetic.Expr
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits

def context (input : Input Nat) : List Nat :=
  [(formulaFields input.1).length,clauseMarks 1 input.1.clauses,literalMarks 1 input.1.clauses,0,0] ++ FlatEncoding.fields input

def scanCode : Code := scannerCode.comp Code.dynamicDropCode
def scanCoefficient : Nat := scannerWeight*(1000000+1)+1000000

theorem scanCode_eval (input : Input Nat) : scanCode.eval (FlatEncoding.fields input) =
    pure [(formulaFields input.1).length,0,0,clauseMarks 1 input.1.clauses,literalMarks 1 input.1.clauses] := by
  simp [scanCode,formulaProjection_eval,scannerCode_eval,Part.bind_eq_bind]

theorem scanCode_fits (input : Input Nat) :
    EvaluatorCodeFits scanCode (FlatEncoding.fields input)
      [(formulaFields input.1).length,0,0,clauseMarks 1 input.1.clauses,literalMarks 1 input.1.clauses]
      (scanCoefficient*(encodedListSpace (FlatEncoding.fields input)+1)) := by
  have scan := scannerCode_fits input.1
  rw [← PeriodicCNF.FieldSavitch.fields_space] at scan
  have projection := formulaProjection_fits input
  rw [← FlatEncoding.fields_space] at projection
  exact comp_linear scan projection

def project (i : Nat) : Code := (Code.get i).comp scanCode
def projectCoefficient (i : Nat) : Nat := (10000*(i+1))*(scanCoefficient+1)+scanCoefficient

def code : Code := Code.prepend (project 0) (Code.prepend (project 3) (Code.prepend (project 4)
  (Code.prepend Code.zero (Code.prepend Code.zero Code.id))))
def coefficient : Nat := 4*(projectCoefficient 0+4*(projectCoefficient 3+4*(projectCoefficient 4+
  4*(10000+4*(10000+10+1)+1)+1)+1)+1)

theorem code_eval (input : Input Nat) : code.eval (FlatEncoding.fields input) = pure (context input) := by
  simp [code,project,Code.prepend,scanCode_eval,context,Part.bind_eq_bind]

theorem code_fits (input : Input Nat) :
    EvaluatorCodeFits code (FlatEncoding.fields input) (context input)
      (coefficient*((FlatEncoding.finEncoding.encode input).length+1)) := by
  have proj (i : Nat) := comp_linear (get_linear i
    [(formulaFields input.1).length,0,0,clauseMarks 1 input.1.clauses,literalMarks 1 input.1.clauses]) (scanCode_fits input)
  have z := zero_unit (FlatEncoding.fields input) (encodedListSpace (FlatEncoding.fields input)+1) le_rfl
  have ident := (EvaluatorCodeFits.id (FlatEncoding.fields input)).mono (idCost_bound _)
  have fit := prepend_linear (proj 0) (prepend_linear (proj 3) (prepend_linear (proj 4)
    (prepend_linear z (prepend_linear z ident))))
  change EvaluatorCodeFits code (FlatEncoding.fields input) (context input)
    (coefficient*(encodedListSpace (FlatEncoding.fields input)+1)) at fit
  rw [FlatEncoding.fields_space] at fit
  exact fit

def formulaField (depth : Nat) (index : Expr) : Expr := .load (index+.literal (depth+6)+var (depth+5))

theorem header_eval (input : Input Nat) (front : List Nat) (i : Fin 6) :
    (var (front.length+i.val)).eval (front++context input) =
      ([(formulaFields input.1).length,clauseMarks 1 input.1.clauses,literalMarks 1 input.1.clauses,0,0,
        (drawingFields input.2).length][i.val]?.getD 0) := by
  rw [eval_var,List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
  fin_cases i <;> simp [context,FlatEncoding.fields]

theorem formulaField_eval (input : Input Nat) (front : List Nat) (index : Expr) :
    (formulaField front.length index).eval (front++context input) =
      (formulaFields input.1)[index.eval (front++context input)]?.getD 0 := by
  have header := header_eval input front ⟨5,by decide⟩
  simp only [List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] at header
  simp only [formulaField,Expr.eval,Op.eval,header]
  let leading := front ++ [(formulaFields input.1).length,clauseMarks 1 input.1.clauses,
    literalMarks 1 input.1.clauses,0,0,(drawingFields input.2).length] ++ drawingFields input.2
  have layout : front++context input = leading++formulaFields input.1 := by simp [leading,context,FlatEncoding.fields,List.append_assoc]
  have size : leading.length = front.length+6+(drawingFields input.2).length := by simp [leading]; omega
  rw [layout,List.getElem?_append_right (by rw [size]; omega)]
  rw [size]
  congr 2
  omega

end LeanTrominoes.PeriodicPlanarSAT.RouteInput
