/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PartrecBoundedAll
import LeanTrominoes.PartrecNatEquality
import LeanTrominoes.PartrecNatCompare
import LeanTrominoes.PartrecAdd
import LeanTrominoes.PartrecMultiply
import LeanTrominoes.PartrecDivision
import LeanTrominoes.PartrecPowerTwo
import LeanTrominoes.PartrecDynamicDrop

/-! # A uniform compiler for bounded arithmetic formulas on flat input fields -/

namespace LeanTrominoes.BoundedArithmetic
open Turing.ToPartrec

inductive Op
  | add | sub | mul | div | mod | eq | lt
  deriving DecidableEq

def Op.eval : Op → Nat → Nat → Nat
  | .add,a,b => a+b
  | .sub,a,b => a-b
  | .mul,a,b => a*b
  | .div,a,b => a/b
  | .mod,a,b => a%b
  | .eq,a,b => if a=b then 1 else 0
  | .lt,a,b => if a<b then 1 else 0

def Op.code : Op → Code
  | .add => Code.natAddCode
  | .sub => Code.subtractCode
  | .mul => Code.natMultiplyCode
  | .div => (Code.get 0).comp Code.divisionCode
  | .mod => (Code.get 1).comp Code.divisionCode
  | .eq => Code.natEqCode
  | .lt => Code.natLtCode

theorem Op.code_eval (op : Op) (a b : Nat) : op.code.eval [a,b] = pure [op.eval a b] := by
  cases op <;> simp [Op.code,Op.eval,Part.bind_eq_bind]

/-- `load` reads a field; quantifiers and local bindings prepend one field to the environment. -/
inductive Expr
  | literal : Nat → Expr
  | load : Expr → Expr
  | binary : Op → Expr → Expr → Expr
  | powerTwo : Expr → Expr
  | ite : Expr → Expr → Expr → Expr
  | letE : Expr → Expr → Expr
  | all : Expr → Expr → Expr

def Expr.eval : Expr → List Nat → Nat
  | .literal n,_ => n
  | .load i,values => values[i.eval values]?.getD 0
  | .binary op a b,values => op.eval (a.eval values) (b.eval values)
  | .powerTwo a,values => 2^(a.eval values)
  | .ite test yes no,values => if test.eval values = 0 then no.eval values else yes.eval values
  | .letE a body,values => body.eval (a.eval values :: values)
  | .all count body,values =>
    (Code.allFrom (fun i => decide (body.eval (i :: values) ≠ 0)) 0 (count.eval values)).toNat

def Expr.code : Expr → Code
  | .literal n => Code.numeral n
  | .load i => (Code.head.comp Code.dynamicDropCode).comp (Code.prepend i.code Code.id)
  | .binary op a b => op.code.comp (Code.prepend a.code b.code)
  | .powerTwo a => Code.powerTwoCode.comp a.code
  | .ite test yes no => Code.branchZero test.code no.code yes.code
  | .letE a body => body.code.comp (Code.prepend a.code Code.id)
  | .all count body => (Code.boundedAll (Code.normalizeBool body.code)).comp
      (Code.prepend count.code Code.id)

private theorem drop_headI_eq_getD (values : List Nat) (index : Nat) :
    (values.drop index).headI = values[index]?.getD 0 := by
  induction index generalizing values with
  | zero => cases values <;> rfl
  | succ index ih => cases values with
    | nil => simp
    | cons a values => simpa using ih values

/-- Every formula compiles to an actual total partial-recursive evaluator program. -/
theorem Expr.code_eval (expr : Expr) (values : List Nat) : expr.code.eval values = pure [expr.eval values] := by
  induction expr generalizing values with
  | literal n => simp [Expr.code,Expr.eval]
  | load i ih => simp [Expr.code,Expr.eval,ih,Part.bind_eq_bind,drop_headI_eq_getD]
  | binary op a b ia ib => simp [Expr.code,Expr.eval,ia,ib,Op.code_eval,Part.bind_eq_bind]
  | powerTwo a ih => simp [Expr.code,Expr.eval,ih,Part.bind_eq_bind]
  | ite test yes no it iy ino =>
    by_cases h : test.eval values = 0
    · simpa [Expr.code,Expr.eval,h] using Code.branchZero_eval_zero_at test.code no.code yes.code
        values (test.eval values) (it values) [no.eval values] (ino values) h
    · simpa [Expr.code,Expr.eval,h] using Code.branchZero_eval_succ_at test.code no.code yes.code
        values (test.eval values) (it values) [yes.eval values] (iy values) (Nat.pos_of_ne_zero h)
  | letE a body ia ib => simp [Expr.code,Expr.eval,ia,ib,Part.bind_eq_bind]
  | all count body ic ib =>
    have leaf (i : Nat) : (Code.normalizeBool body.code).eval (i :: values) =
        pure [(decide (body.eval (i :: values) ≠ 0)).toNat] := by
      have normalized := Code.normalizeBool_eval_at body.code (i :: values) (body.eval (i :: values)) (ib _)
      by_cases h : body.eval (i :: values) = 0 <;> simpa [h] using normalized
    have loop := Code.boundedAll_eval (Code.normalizeBool body.code) values
      (fun i => decide (body.eval (i :: values) ≠ 0)) leaf (count.eval values)
    simpa [Expr.code,Expr.eval,ic,Part.bind_eq_bind] using loop

/-- Every evaluated subexpression, including every bounded-quantifier environment,
has the claimed binary size. This is the semantic premise of the space compiler. -/
def Expr.Safe (bits : Nat) : Expr → List Nat → Prop
  | .literal n,_ => (Computability.encodeNat n).length ≤ bits
  | .load i,values => i.Safe bits values ∧ (Computability.encodeNat ((.load i : Expr).eval values)).length ≤ bits
  | .binary op a b,values => a.Safe bits values ∧ b.Safe bits values ∧
      (Computability.encodeNat (op.eval (a.eval values) (b.eval values))).length ≤ bits
  | .powerTwo a,values => a.Safe bits values ∧ (Computability.encodeNat (2^a.eval values)).length ≤ bits
  | .ite test yes no,values => test.Safe bits values ∧ yes.Safe bits values ∧ no.Safe bits values
  | .letE a body,values => a.Safe bits values ∧ body.Safe bits (a.eval values :: values)
  | .all count body,values => count.Safe bits values ∧ 1 ≤ bits ∧
      ∀ i, i ≤ count.eval values → body.Safe bits (i :: values)

theorem Expr.Safe.value_bits {expr : Expr} {bits : Nat} {values : List Nat}
    (safe : expr.Safe bits values) : (Computability.encodeNat (expr.eval values)).length ≤ bits := by
  induction expr generalizing values with
  | literal n => exact safe
  | load i ih => exact safe.2
  | binary op a b ia ib => exact safe.2.2
  | powerTwo a ih => exact safe.2
  | ite test yes no it iy ino =>
    simp only [Expr.eval]
    split
    · exact ino safe.2.2
    · exact iy safe.2.1
  | letE a body ia ib => exact ib safe.2
  | all count body ic ib =>
    have h := safe.2.1
    change (Computability.encodeNat (Bool.toNat _)).length ≤ bits
    cases Code.allFrom (fun i => decide (body.eval (i :: values) ≠ 0)) 0 (count.eval values)
    · change 0 ≤ bits; omega
    · change 1 ≤ bits; exact h

end LeanTrominoes.BoundedArithmetic
