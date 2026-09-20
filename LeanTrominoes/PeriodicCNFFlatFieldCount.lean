/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFFlatScannerCodeSpace

/-! # Computing the flat CNF field count from clause headers -/
namespace LeanTrominoes.PeriodicCNF.FlatScanner
open Turing Turing.ToPartrec Turing.PartrecToTM2
open BoundedArithmetic BoundedArithmetic.Expr PeriodicCNFFlatEncoding
open Turing.PartrecToTM2.EvaluatorCodeFits

def countStep (v : List Nat) : List Nat :=
  (v[0]?.getD 0+1+4*v[1]?.getD 0) :: v.drop (2+4*v[1]?.getD 0)

def countStepCode : Code := Code.prepend (var 0+1+4*var 1).code
  (Code.dynamicDropCode.comp (Code.prepend (2+4*var 1).code Code.id))

theorem countStepCode_eval (v : List Nat) : countStepCode.eval v = pure (countStep v) := by
  simp [countStepCode,Expr.code_eval,Part.bind_eq_bind,countStep,Expr.eval,Op.eval]

private theorem literalFields_length (ls : List (PeriodicLiteral Nat)) :
    (ls.flatMap literalFields).length = 4*ls.length := by
  induction ls with
  | nil => simp
  | cons l ls ih => simp [literalFields,ih]; omega

theorem countStep_clause (cursor : Nat) (c : PeriodicClause Nat) (cs : List (PeriodicClause Nat)) :
    countStep (cursor :: (c::cs).flatMap clauseFields) =
      (cursor+1+4*c.length) :: cs.flatMap clauseFields := by
  simp only [countStep,List.flatMap_cons,clauseFields,List.cons_append,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some]
  rw [show 2+4*c.length = (4*c.length+1)+1 by omega]
  simp only [List.drop_succ_cons]
  rw [← literalFields_length c,List.drop_left]

theorem countStep_iterate (cs : List (PeriodicClause Nat)) (cursor : Nat) :
    (countStep^[cs.length]) (cursor :: cs.flatMap clauseFields) =
      [cursor+(cs.flatMap clauseFields).length] := by
  induction cs generalizing cursor with
  | nil => simp
  | cons c cs ih =>
    rw [List.length_cons,Function.iterate_succ_apply,countStep_clause,ih]
    simp only [List.flatMap_cons,clauseFields,List.length_append,List.length_cons,literalFields_length]
    congr 1 <;> omega

theorem countStep_partial (cs : List (PeriodicClause Nat)) (cursor n : Nat) (hn : n ≤ cs.length) :
    (countStep^[n]) (cursor :: cs.flatMap clauseFields) =
      (cursor+((cs.take n).flatMap clauseFields).length) :: (cs.drop n).flatMap clauseFields := by
  induction cs generalizing cursor n with
  | nil =>
    have h : n=0 := by simpa using hn
    subst n
    simp
  | cons c cs ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [Function.iterate_succ_apply,countStep_clause,ih _ _ (by simpa using hn)]
      simp only [List.take_succ_cons,List.drop_succ_cons,List.flatMap_cons,clauseFields,
        List.length_append,List.length_cons,literalFields_length]
      congr 1 <;> omega

def fieldCountInputCode : Code := Code.prepend (Code.get 0)
  (Code.prepend Code.one (Code.drop 1))

def fieldCountCode : Code := (Code.flatIterate countStepCode).comp fieldCountInputCode

theorem fieldCountCode_eval (f : PeriodicCNF Nat) :
    fieldCountCode.eval (formulaFields f) = pure [(formulaFields f).length] := by
  have h := Code.flatIterate_eval countStepCode countStep countStepCode_eval
    f.clauses.length (1 :: f.clauses.flatMap clauseFields)
  rw [countStep_iterate] at h
  simpa [fieldCountCode,fieldCountInputCode,formulaFields,Part.bind_eq_bind,Nat.add_comm] using h

/-- Build the scanner input directly from the original encoding. -/
def scanInputCode : Code := Code.prepend fieldCountCode
  (Code.prepend Code.one (Code.prepend Code.zero
    (Code.prepend (Code.get 0) (Code.prepend Code.zero
      (Code.prepend Code.zero (Code.drop 1))))))

def scannerCode : Code := (Code.flatIterate stepCode).comp scanInputCode

theorem scannerCode_eval (f : PeriodicCNF Nat) :
    scannerCode.eval (formulaFields f) =
      pure [(formulaFields f).length,0,0,clauseMarks 1 f.clauses,literalMarks 1 f.clauses] := by
  have input : scanInputCode.eval (formulaFields f) =
      pure ((formulaFields f).length :: (initial f).fields) := by
    simp only [scanInputCode,Code.prepend_eval_eq,fieldCountCode_eval,Part.bind_eq_bind]
    simp [formulaFields,initial,State.fields,State.pending]
  simpa [scannerCode,input,Part.bind_eq_bind,scan_cursor,(scan_masks f).1,(scan_masks f).2]
    using scanCode_eval f

end LeanTrominoes.PeriodicCNF.FlatScanner
