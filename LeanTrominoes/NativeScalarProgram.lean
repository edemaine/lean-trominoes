/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BoundedArithmeticCountSpace

/-! # Composing total scalar queries with linear evaluator-space certificates

Arithmetic queries, counting, bindings, and bounded quantifiers can share a
flat input without materializing tables of their answers.
-/
namespace LeanTrominoes.NativeScalar
open BoundedArithmetic BoundedArithmetic.Expr
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits

structure Program where
  value : List Nat → Nat
  code : Code
  coefficient : Nat
  evaluates : ∀ values, code.eval values = pure [value values]
  fits : ∀ values, EvaluatorCodeFits code values [value values] (coefficient*(encodedListSpace values+1))

def arithmetic (expr : Expr) (allowed : expr.noPower = true) : Program where
  value := expr.eval
  code := expr.code
  coefficient := expr.weight*(expr.radius+1)
  evaluates := expr.code_eval
  fits values := expr.code_fits_automatic values allowed

def bindCoefficient (first second : Nat) : Nat := second*(4*(first+10+1)+1)+4*(first+10+1)

def bind (first second : Program) : Program where
  value values := second.value (first.value values :: values)
  code := second.code.comp (Code.prepend first.code Code.id)
  coefficient := bindCoefficient first.coefficient second.coefficient
  evaluates values := by simp [Code.prepend,first.evaluates,second.evaluates,Part.bind_eq_bind]
  fits values := by
    have ident := (EvaluatorCodeFits.id values).mono (idCost_bound values)
    exact comp_linear (second.fits _) (prepend_linear (first.fits values) ident)

def count (bound : Program) (body : Expr) (allowed : body.noPower = true) : Program where
  value values := Count.count body values (bound.value values)
  code := (Count.code body).comp (Code.prepend bound.code Code.id)
  coefficient := bindCoefficient bound.coefficient (Count.coefficient body)
  evaluates values := by simp [Code.prepend,bound.evaluates,Count.code_eval,Part.bind_eq_bind]
  fits values := by
    have ident := (EvaluatorCodeFits.id values).mono (idCost_bound values)
    exact comp_linear (Count.code_fits body allowed values _) (prepend_linear (bound.fits values) ident)

def normalize (p : Program) : Program := bind p (arithmetic (.ite (var 0) 1 0) (by decide))

theorem normalize_value (p : Program) (values : List Nat) :
    (normalize p).value values = (decide (p.value values ≠ 0)).toNat := by
  by_cases h : p.value values=0 <;> simp [normalize,bind,arithmetic,Expr.eval,var,h]

def allValue (bound body : Program) (values : List Nat) : Nat :=
  (Code.allFrom (fun i => decide (body.value (i::values) ≠ 0)) 0 (bound.value values)).toNat

def allCoefficient (body : Program) : Nat := 10000000*((normalize body).coefficient+2)

theorem all_fits (body : Program) (values : List Nat) (n : Nat) :
    EvaluatorCodeFits (Code.boundedAll (normalize body).code) (n::values)
      [(Code.allFrom (fun i => decide (body.value (i::values) ≠ 0)) 0 n).toNat]
      (allCoefficient body*(encodedListSpace (n::values)+1)) := by
  have hbits : (Computability.encodeNat n).length ≤ encodedListSpace (n::values) := by
    simp only [encodedListSpace_cons]; omega
  have fitted := boundedAll_uniform values (fun i => decide (body.value (i::values) ≠ 0)) n
    (encodedListSpace (n::values)) ((normalize body).coefficient*(encodedListSpace (n::values)+1)) hbits (by
      intro i hi
      have fit := (normalize body).fits (i::values)
      rw [normalize_value] at fit
      apply fit.mono
      apply Nat.mul_le_mul_left
      have hi' := listCodeEncodeNat_length_mono hi
      simp only [encodedListSpace_cons]
      omega)
  apply fitted.mono
  have h : encodedListSpace values ≤ encodedListSpace (n::values) := by simp [encodedListSpace_cons]
  unfold allCoefficient
  nlinarith

def all (bound body : Program) : Program where
  value := allValue bound body
  code := (Code.boundedAll (normalize body).code).comp (Code.prepend bound.code Code.id)
  coefficient := bindCoefficient bound.coefficient (allCoefficient body)
  evaluates values := by
    have leaf (i : Nat) : (normalize body).code.eval (i::values) =
        pure [(decide (body.value (i::values) ≠ 0)).toNat] := by
      rw [(normalize body).evaluates,normalize_value]
    have args : (Code.prepend bound.code Code.id).eval values = pure (bound.value values :: values) := by
      simp [Code.prepend,bound.evaluates]
    simp [args,Code.boundedAll_eval _ _ _ leaf,allValue,Part.bind_eq_bind]
  fits values := by
    have ident := (EvaluatorCodeFits.id values).mono (idCost_bound values)
    exact comp_linear (all_fits body values _) (prepend_linear (bound.fits values) ident)

theorem all_value_ne_zero (bound body : Program) (values : List Nat) :
    (all bound body).value values ≠ 0 ↔ ∀ i < bound.value values, body.value (i::values) ≠ 0 := by
  have truth (b : Bool) : b.toNat ≠ 0 ↔ b=true := by cases b <;> decide
  simp only [all,allValue,truth,Code.allFrom_eq_true_iff,Nat.zero_le,Nat.zero_add,
    forall_true_left,decide_eq_true_eq]

end LeanTrominoes.NativeScalar
