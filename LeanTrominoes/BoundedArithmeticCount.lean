/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BoundedArithmeticLogic
import LeanTrominoes.PartrecLinearAdaptersSpace
import LeanTrominoes.PartrecFlatIterationUniformSpace

/-! # Counting bounded arithmetic witnesses without storing them

The native program keeps an accumulator and an index before its unchanged
input fields. This supplies the ranks needed to locate incidence vertices.
-/
namespace LeanTrominoes.BoundedArithmetic.Count
open Expr Turing Turing.ToPartrec Turing.PartrecToTM2
open Turing.PartrecToTM2.EvaluatorCodeFits

def indicator (body : Expr) (values : List Nat) (i : Nat) : Nat :=
  (decide (body.eval (i::values) ≠ 0)).toNat

def count (body : Expr) (values : List Nat) (n : Nat) : Nat :=
  ((List.range n).map (indicator body values)).sum

theorem count_zero (body : Expr) (values : List Nat) : count body values 0 = 0 := rfl

theorem count_succ (body : Expr) (values : List Nat) (n : Nat) :
    count body values (n+1) = count body values n + indicator body values n := by
  simp [count,List.range_succ,List.map_append,List.sum_append]

theorem indicator_le (body : Expr) (values : List Nat) (i : Nat) : indicator body values i ≤ 1 := by
  unfold indicator
  cases decide (body.eval (i::values) ≠ 0) <;> decide

theorem count_le (body : Expr) (values : List Nat) (n : Nat) : count body values n ≤ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [count_succ]; have h := indicator_le body values n; omega

theorem count_eq_length_filter (body : Expr) (values : List Nat) (n : Nat) :
    count body values n = ((List.range n).filter fun i => decide (body.eval (i::values) ≠ 0)).length := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [count_succ,List.range_succ,List.filter_append,List.length_append,ih]
    by_cases h : body.eval (n::values)=0 <;> simp [indicator,h]

def boolExpr (body : Expr) : Expr := .ite body 1 0

theorem boolExpr_eval (body : Expr) (values : List Nat) :
    (boolExpr body).eval values = (decide (body.eval values ≠ 0)).toNat := by
  by_cases h : body.eval values = 0 <;> simp [boolExpr,Expr.eval,h]

def step (body : Expr) (v : List Nat) : List Nat :=
  [v[0]?.getD 0+(decide (body.eval v.tail ≠ 0)).toNat,v[1]?.getD 0+1] ++ v.drop 2

def stepCode (body : Expr) : Code :=
  Code.prepend ((var 0+var 1 : Expr).code.comp
    (Code.prepend (Code.get 0) ((boolExpr body).code.comp (Code.drop 1))))
    (Code.prepend (var 1+1 : Expr).code (Code.drop 2))

theorem stepCode_eval (body : Expr) (v : List Nat) : (stepCode body).eval v = pure (step body v) := by
  simp [stepCode,Code.prepend,Expr.code_eval,eval_var,Expr.eval,Op.eval,boolExpr_eval,
    step,Part.bind_eq_bind,List.drop_one]

theorem iterate_step (body : Expr) (values : List Nat) (n : Nat) :
    ((step body)^[n]) (0::0::values) = count body values n :: n :: values := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih,count_succ]
    simp [step,indicator]

def inputCode : Code := Code.prepend (Code.get 0)
  (Code.prepend Code.zero (Code.prepend Code.zero (Code.drop 1)))

def code (body : Expr) : Code :=
  (Code.get 0).comp ((Code.flatIterate (stepCode body)).comp inputCode)

theorem code_eval (body : Expr) (values : List Nat) (n : Nat) :
    (code body).eval (n::values) = pure [count body values n] := by
  simp [code,inputCode,Code.prepend,Code.flatIterate_eval _ _ (stepCode_eval body),
    iterate_step,Part.bind_eq_bind]

def expressionCoefficient (expr : Expr) : Nat := expr.weight*(expr.radius+1)
def stepCoefficient (body : Expr) : Nat :=
  4*(expressionCoefficient (var 0+var 1)*(4*(10000+
    (expressionCoefficient (boolExpr body)*(20000+1)+20000)+1)+1)+
    4*(10000+(expressionCoefficient (boolExpr body)*(20000+1)+20000)+1)+
    4*(expressionCoefficient (var 1+1)+30000+1)+1)

theorem stepCode_fits (body : Expr) (allowed : body.noPower = true) (v : List Nat) :
    EvaluatorCodeFits (stepCode body) v (step body v)
      (stepCoefficient body*(encodedListSpace v+1)) := by
  have hb : (boolExpr body).noPower = true := by simp [boolExpr,Expr.noPower,allowed]
  have test := comp_linear ((boolExpr body).code_fits_automatic (v.drop 1) hb) (drop_linear 1 v)
  have args := prepend_linear (get_linear 0 v) test
  have sum := comp_linear ((var 0+var 1 : Expr).code_fits_automatic _ (by decide)) args
  have rest := prepend_linear ((var 1+1 : Expr).code_fits_automatic v (by decide)) (drop_linear 2 v)
  have fit := prepend_linear sum rest
  simpa only [stepCode,step,stepCoefficient,expressionCoefficient,boolExpr_eval,
    List.drop_one,eval_var,Expr.eval,Op.eval,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,List.singleton_append,List.cons_append,
    List.nil_append] using fit

end LeanTrominoes.BoundedArithmetic.Count
