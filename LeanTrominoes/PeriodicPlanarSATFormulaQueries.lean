/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarSATRouteInput
import LeanTrominoes.PeriodicCNFIncidenceFieldRanks
import LeanTrominoes.BoundedArithmeticInsertedFields

/-! # Reusing formula-address queries inside the shared route environment -/
namespace LeanTrominoes.PeriodicPlanarSAT.RouteInput
open BoundedArithmetic BoundedArithmetic.Expr PeriodicCNFFlatEncoding
open PeriodicCNF.FlatScanner PeriodicCNF.IncidenceFields

def formulaQuery (extra : Nat) (expr : Expr) : Expr := (expr.skipBlock 6).insertFields 1 extra

theorem formulaQuery_eval (expr : Expr) (input : Input Nat) (front : List Nat) (p : Nat) :
    (formulaQuery front.length expr).eval (p::(front++context input)) =
      expr.eval (p::PeriodicCNF.FieldSavitch.suffix input.1) := by
  have inserted := Expr.insertFields_eval (expr.skipBlock 6) [p] front (context input)
  simp only [List.length_cons,List.length_nil,List.cons_append,List.nil_append] at inserted
  rw [formulaQuery,inserted]
  have skipped := Expr.skipBlock_eval expr
    [p,(formulaFields input.1).length,clauseMarks 1 input.1.clauses,literalMarks 1 input.1.clauses,0,0]
    (FlatEncoding.drawingFields input.2) (formulaFields input.1)
  simpa only [context,FlatEncoding.fields,PeriodicCNF.FieldSavitch.suffix,PeriodicCNF.FieldPredicate.input,
    PeriodicCNF.FieldPredicate.context,List.length_cons,List.length_nil,Nat.reduceAdd,
    List.cons_append,List.nil_append] using skipped

theorem formulaQuery_noPower (extra : Nat) (expr : Expr) : (formulaQuery extra expr).noPower=expr.noPower := by
  rw [formulaQuery,Expr.insertFields_noPower,Expr.skipBlock_noPower]

theorem formulaQuery_count (expr : Expr) (input : Input Nat) (front : List Nat) (bound : Nat) :
    Count.count (formulaQuery front.length expr) (front++context input) bound =
      Count.count expr (PeriodicCNF.FieldSavitch.suffix input.1) bound := by
  unfold Count.count
  congr 1
  apply List.map_congr_left
  intro p _
  simp only [Count.indicator,formulaQuery_eval]

def countQuery (extra : Nat) (bound expr : Expr) (hbound : bound.noPower=true) (hexpr : expr.noPower=true) : NativeScalar.Program :=
  NativeScalar.count (NativeScalar.arithmetic bound hbound) (formulaQuery extra expr)
    (by rw [formulaQuery_noPower,hexpr])

theorem countQuery_value (bound expr : Expr) (hbound : bound.noPower=true) (hexpr : expr.noPower=true)
    (input : Input Nat) (front : List Nat) :
    (countQuery front.length bound expr hbound hexpr).value (front++context input) =
      Count.count expr (PeriodicCNF.FieldSavitch.suffix input.1) (bound.eval (front++context input)) :=
  formulaQuery_count expr input front _

end LeanTrominoes.PeriodicPlanarSAT.RouteInput
