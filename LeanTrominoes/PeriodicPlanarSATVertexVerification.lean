/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicDrawingVertexPredicate
import LeanTrominoes.PeriodicPlanarSATIncidenceCountVerification

/-! # Native vertex and incidence-count compatibility verification -/
namespace LeanTrominoes.PeriodicGridDrawing.VertexPredicate
open BoundedArithmetic BoundedArithmetic.Expr

instance (orbit : Bool) (d : PeriodicGridDrawing) : Decidable (Valid orbit d) := by
  unfold Valid PositionInFundamentalSquare
  split <;> infer_instance

def result (orbit : Bool) (d : PeriodicGridDrawing) : Bool := decide (Valid orbit d)

theorem decision_eval (orbit : Bool) (d : PeriodicGridDrawing) :
    (decision orbit).eval (Arithmetic.fields d) = (result orbit d).toNat := by
  have h := predicate_truth orbit d
  unfold Truth at h
  by_cases test : (predicate orbit).eval (Arithmetic.fields d)=0
  · have no : ¬Valid orbit d := fun yes => h.mpr yes test
    simp [decision,result,Expr.eval,test,no]
  · simp [decision,result,Expr.eval,test,h.mp test]

end LeanTrominoes.PeriodicGridDrawing.VertexPredicate

namespace LeanTrominoes.PeriodicPlanarSAT.VertexVerification
open FlatEncoding BoundedArithmetic PeriodicGridDrawing.VertexPredicate
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits

def expression (orbit : Bool) : Expr := (decision orbit).slice 0

def vertexCoefficient (orbit : Bool) : Nat := (expression orbit).weight*((expression orbit).radius+1)

theorem expression_eval (orbit : Bool) (input : Input Nat) :
    (expression orbit).eval (fields input) = (result orbit input.2).toNat := by
  have h := Expr.slice_eval (decision orbit) [] (drawingFields input.2) (PeriodicCNFFlatEncoding.formulaFields input.1)
  simpa only [expression,FlatEncoding.fields,List.length_nil,List.nil_append,decision_eval] using h

theorem vertexCode_eval (orbit : Bool) (input : Input Nat) :
    (expression orbit).code.eval (fields input) = pure [(result orbit input.2).toNat] := by
  rw [Expr.code_eval,expression_eval]

theorem vertexCode_fits (orbit : Bool) (input : Input Nat) :
    EvaluatorCodeFits (expression orbit).code (fields input) [(result orbit input.2).toNat]
      (vertexCoefficient orbit*((finEncoding.encode input).length+1)) := by
  have allowed : (expression orbit).noPower = true := by
    rw [expression,Expr.slice_noPower,decision_noPower]
  have fit := (expression orbit).code_fits_automatic (fields input) allowed
  rw [expression_eval,fields_space] at fit
  exact fit

def code (orbit : Bool) : Code := Code.boolAnd IncidenceCounts.code (expression orbit).code

def check (orbit : Bool) (input : Input Nat) : Bool := IncidenceCounts.result input && result orbit input.2

def coefficient (orbit : Bool) : Nat := 1000*(1+IncidenceCounts.coefficient+vertexCoefficient orbit+2)

theorem code_eval (orbit : Bool) (input : Input Nat) :
    (code orbit).eval (fields input) = pure [(check orbit input).toNat] := by
  have h := Code.boolAnd_eval_at IncidenceCounts.code (expression orbit).code (fields input)
    (IncidenceCounts.result input).toNat (result orbit input.2).toNat
    (IncidenceCounts.code_eval input) (vertexCode_eval orbit input)
  cases ha : IncidenceCounts.result input <;> cases hb : result orbit input.2 <;>
    simpa [code,check,ha,hb] using h

theorem code_fits (orbit : Bool) (input : Input Nat) :
    EvaluatorCodeFits (code orbit) (fields input) [(check orbit input).toNat]
      (coefficient orbit*((finEncoding.encode input).length+1)) := by
  have fit := boolAnd_bool (IncidenceCounts.code_fits input) (vertexCode_fits orbit input)
  rw [fields_space] at fit
  apply fit.mono
  unfold coefficient
  nlinarith

theorem check_correct (orbit : Bool) (input : Input Nat) :
    check orbit input = true ↔ IncidenceCounts.Valid input ∧ PeriodicGridDrawing.VertexPredicate.Valid orbit input.2 := by
  simp [check,IncidenceCounts.result,result]

theorem orbit_compatible_iff (input : Input Nat) :
    PeriodicGridDrawing.OrbitCertificate.Compatible input.1.incidenceGraph input.2 ↔
      check true input = true ∧ input.2.RoutesMatch input.1.incidenceGraph := by
  rw [check_correct]
  simp only [PeriodicGridDrawing.OrbitCertificate.Compatible,IncidenceCounts.Valid,PeriodicGridDrawing.VertexPredicate.Valid,if_true]
  tauto

theorem finite_compatible_iff (input : Input Nat) :
    PeriodicGridDrawing.FiniteCertificate.Compatible input.1.incidenceGraph input.2 ↔
      check false input = true ∧ input.2.RoutesMatch input.1.incidenceGraph := by
  rw [check_correct]
  simp only [PeriodicGridDrawing.FiniteCertificate.Compatible,IncidenceCounts.Valid,PeriodicGridDrawing.VertexPredicate.Valid,Bool.false_eq_true,if_false]
  tauto

end LeanTrominoes.PeriodicPlanarSAT.VertexVerification
