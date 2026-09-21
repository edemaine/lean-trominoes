/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFIncidenceFieldCount
import LeanTrominoes.PeriodicDrawingArithmeticRouteCount
import LeanTrominoes.PeriodicPlanarSATGridGuard

/-! # Native incidence vertex and edge count checks -/
namespace LeanTrominoes.PeriodicPlanarSAT.IncidenceCounts
open FlatEncoding BoundedArithmetic BoundedArithmetic.Expr
open PeriodicCNF PeriodicCNFFlatEncoding

-- Distinct variables, formula field count, drawing field count, drawing, formula.
def context (input : Input Nat) : List Nat :=
  input.1.variableOccurrences.dedup.length :: (formulaFields input.1).length :: FlatEncoding.fields input

def clauses : Expr := .load (var 2+3)
def literals : Expr := (var 1-1-clauses)/4
def routes : Expr := .load (7+6*var 5+2*var 6)
def predicate : Expr := andE (eqE (var 6) (var 0+clauses)) (eqE routes literals)
def decision : Expr := .ite predicate 1 0

def Valid (input : Input Nat) : Prop :=
  input.2.vertexPositions.length = input.1.incidenceGraph.vertices.length ∧
    input.2.edgeRoutes.length = input.1.incidenceGraph.edges.length

instance (input : Input Nat) : Decidable (Valid input) := by unfold Valid; infer_instance

def result (input : Input Nat) : Bool := decide (Valid input)

theorem clauses_eval (input : Input Nat) : clauses.eval (context input) = input.1.clauses.length := by
  simp only [clauses,Expr.eval,eval_var,Op.eval,context,FlatEncoding.fields,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some]
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp [formulaFields]

theorem literals_eval (input : Input Nat) : literals.eval (context input) = input.1.presentationLiteralCount := by
  change (((var 1).eval (context input)-1-clauses.eval (context input))/4) = _
  rw [clauses_eval]
  change (((formulaFields input.1).length-1-input.1.clauses.length)/4) = _
  rw [formulaFields_length]
  have h : literalCount input.1 = input.1.presentationLiteralCount := by
    simp [literalCount,presentationLiteralCount,List.length_flatten]
  rw [h]
  omega

theorem vertices_eval (input : Input Nat) :
    (var 6).eval (context input) = input.2.vertexPositions.length := by
  simp [context,FlatEncoding.fields,drawingFields,PeriodicGridDrawing.Arithmetic.fields,eval_var]

theorem segments_eval (input : Input Nat) :
    (var 5).eval (context input) = input.2.indexedSegments.length := by
  simp [context,FlatEncoding.fields,drawingFields,PeriodicGridDrawing.Arithmetic.fields,eval_var]

theorem routes_eval (input : Input Nat) : routes.eval (context input) = input.2.edgeRoutes.length := by
  change (context input)[7+6*(var 5).eval (context input)+2*(var 6).eval (context input)]?.getD 0 = _
  rw [segments_eval,vertices_eval]
  have h := PeriodicGridDrawing.Arithmetic.routeCount_field input.2
    [input.1.variableOccurrences.dedup.length,(formulaFields input.1).length,(drawingFields input.2).length]
    (formulaFields input.1)
  simpa only [context,FlatEncoding.fields,List.length_cons,List.length_nil,Nat.reduceAdd,
    List.cons_append,List.nil_append,List.append_assoc] using h

theorem predicate_truth (input : Input Nat) : predicate.Truth (context input) ↔ Valid input := by
  simp only [predicate,truth_and,truth_eq,eval_add,vertices_eval,clauses_eval,routes_eval,literals_eval]
  have atomCount : (var 0).eval (context input) = input.1.variableOccurrences.dedup.length := rfl
  rw [atomCount]
  simp only [Valid,incidenceGraph_edges_length]
  have vertices : input.1.incidenceGraph.vertices.length =
      input.1.variableOccurrences.dedup.length+input.1.clauses.length := by
    simp [incidenceGraph,incidenceVariableVertices,incidenceClauseVertices]
  rw [vertices]

theorem decision_eval (input : Input Nat) : decision.eval (context input) = (result input).toNat := by
  have h := predicate_truth input
  unfold Truth at h
  by_cases test : predicate.eval (context input)=0
  · have no : ¬Valid input := fun yes => h.mpr yes test
    simp [decision,result,Expr.eval,test,no]
  · simp [decision,result,Expr.eval,test,h.mp test]

theorem decision_noPower : decision.noPower = true := by decide

end LeanTrominoes.PeriodicPlanarSAT.IncidenceCounts
