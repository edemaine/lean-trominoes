/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.NativeRouteCursor

/-! # Scalar adapters for composed route queries -/
namespace LeanTrominoes.NativeScalar
open BoundedArithmetic BoundedArithmetic.Expr
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits

def drop (n : Nat) (p : Program) : Program where
  value values := p.value (values.drop n)
  code := p.code.comp (Code.drop n)
  coefficient := p.coefficient*(10000*(n+1)+1)+10000*(n+1)
  evaluates values := by simp [p.evaluates,Part.bind_eq_bind]
  fits values := comp_linear (p.fits (values.drop n)) (drop_linear n values)

def combine (left right : Program) (expr : Expr) (allowed : expr.noPower = true) : Program :=
  bind left (bind (drop 1 right) (arithmetic expr allowed))

def implies (test body : Program) : Program := combine test body (impE (var 1) (var 0)) (by decide)

theorem implies_value_ne_zero (test body : Program) (values : List Nat) :
    (implies test body).value values ≠ 0 ↔ (test.value values ≠ 0 → body.value values ≠ 0) := by
  change (impE (var 1) (var 0)).Truth (body.value values :: test.value values :: values) ↔ _
  rw [truth_imp]
  rfl

def cursor (count start : Program) : Program where
  value values := NativeRouteCursor.advance values (count.value values) (start.value values)
  code := NativeRouteCursor.code.comp (Code.prepend count.code (Code.prepend start.code Code.id))
  coefficient := NativeRouteCursor.coefficient*(4*(count.coefficient+4*(start.coefficient+10+1)+1)+1)+
    4*(count.coefficient+4*(start.coefficient+10+1)+1)
  evaluates values := by simp [Code.prepend,count.evaluates,start.evaluates,NativeRouteCursor.code_eval,Part.bind_eq_bind]
  fits values := by
    have ident := (EvaluatorCodeFits.id values).mono (idCost_bound values)
    exact comp_linear (NativeRouteCursor.code_fits values (count.value values) (start.value values))
      (prepend_linear (count.fits values) (prepend_linear (start.fits values) ident))

end LeanTrominoes.NativeScalar
