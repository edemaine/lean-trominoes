/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PartrecBoundedArithmeticAutomaticSpace

/-! # Logical notation and semantics for compiled bounded formulas -/

namespace LeanTrominoes.BoundedArithmetic.Expr

instance (n : Nat) : OfNat Expr n := ⟨.literal n⟩
instance : Add Expr := ⟨.binary .add⟩
instance : Sub Expr := ⟨.binary .sub⟩
instance : Mul Expr := ⟨.binary .mul⟩
instance : Div Expr := ⟨.binary .div⟩
instance : Mod Expr := ⟨.binary .mod⟩

def var (index : Nat) : Expr := .load (.literal index)
def eqE (a b : Expr) : Expr := .binary .eq a b
def ltE (a b : Expr) : Expr := .binary .lt a b
def notE (a : Expr) : Expr := eqE a 0
def andE (a b : Expr) : Expr := .ite a b 0
def orE (a b : Expr) : Expr := .ite a 1 b
def impE (a b : Expr) : Expr := .ite a b 1
def leE (a b : Expr) : Expr := notE (ltE b a)
def existsE (count body : Expr) : Expr := notE (.all count (notE body))

def Truth (expr : Expr) (values : List Nat) : Prop := expr.eval values ≠ 0

@[simp] theorem eval_literal (n : Nat) (values : List Nat) : (.literal n : Expr).eval values = n := rfl
@[simp] theorem eval_var (index : Nat) (values : List Nat) : (var index).eval values = values[index]?.getD 0 := rfl
@[simp] theorem eval_add (a b : Expr) (values : List Nat) : (a+b).eval values = a.eval values+b.eval values := rfl
@[simp] theorem eval_sub (a b : Expr) (values : List Nat) : (a-b).eval values = a.eval values-b.eval values := rfl
@[simp] theorem eval_mul (a b : Expr) (values : List Nat) : (a*b).eval values = a.eval values*b.eval values := rfl
@[simp] theorem eval_div (a b : Expr) (values : List Nat) : (a/b).eval values = a.eval values/b.eval values := rfl
@[simp] theorem eval_mod (a b : Expr) (values : List Nat) : (a%b).eval values = a.eval values%b.eval values := rfl
@[simp] theorem eval_nat (n : Nat) (values : List Nat) : (OfNat.ofNat n : Expr).eval values = n := rfl

@[simp] theorem truth_eq (a b : Expr) (values : List Nat) : (eqE a b).Truth values ↔ a.eval values = b.eval values := by
  simp [Truth,eqE,Expr.eval,Op.eval]

@[simp] theorem truth_lt (a b : Expr) (values : List Nat) : (ltE a b).Truth values ↔ a.eval values < b.eval values := by
  simp [Truth,ltE,Expr.eval,Op.eval]

@[simp] theorem truth_not (a : Expr) (values : List Nat) : (notE a).Truth values ↔ ¬a.Truth values := by
  rw [notE,truth_eq]
  simp [Truth,Expr.eval]

@[simp] theorem truth_and (a b : Expr) (values : List Nat) : (andE a b).Truth values ↔ a.Truth values ∧ b.Truth values := by
  by_cases h : a.eval values = 0 <;> simp [Truth,andE,Expr.eval,h]

@[simp] theorem truth_or (a b : Expr) (values : List Nat) : (orE a b).Truth values ↔ a.Truth values ∨ b.Truth values := by
  by_cases h : a.eval values = 0 <;> simp [Truth,orE,Expr.eval,h]

@[simp] theorem truth_imp (a b : Expr) (values : List Nat) : (impE a b).Truth values ↔ (a.Truth values → b.Truth values) := by
  by_cases h : a.eval values = 0 <;> simp [Truth,impE,Expr.eval,h]

@[simp] theorem truth_le (a b : Expr) (values : List Nat) : (leE a b).Truth values ↔ a.eval values ≤ b.eval values := by
  simp [leE]

private theorem bool_toNat_ne_zero (b : Bool) : b.toNat ≠ 0 ↔ b = true := by cases b <;> decide

@[simp] theorem truth_bit (a b : Expr) (values : List Nat) :
    (.testBit a b : Expr).Truth values ↔ (a.eval values).testBit (b.eval values) = true := by
  exact bool_toNat_ne_zero _

@[simp] theorem truth_all (count body : Expr) (values : List Nat) :
    (.all count body : Expr).Truth values ↔ ∀ i < count.eval values, body.Truth (i :: values) := by
  simp only [Truth,Expr.eval,bool_toNat_ne_zero,Turing.ToPartrec.Code.allFrom_eq_true_iff,
    Nat.zero_le,Nat.zero_add,true_implies,decide_eq_true_eq]

@[simp] theorem truth_exists (count body : Expr) (values : List Nat) :
    (existsE count body).Truth values ↔ ∃ i < count.eval values, body.Truth (i :: values) := by
  classical
  simp [existsE]

@[simp] theorem noPower_var (i : Nat) : (var i).noPower = true := rfl
@[simp] theorem noPower_nat (n : Nat) : (OfNat.ofNat n : Expr).noPower = true := rfl
@[simp] theorem noPower_add (a b : Expr) : (a+b).noPower = (a.noPower && b.noPower) := rfl
@[simp] theorem noPower_sub (a b : Expr) : (a-b).noPower = (a.noPower && b.noPower) := rfl
@[simp] theorem noPower_mul (a b : Expr) : (a*b).noPower = (a.noPower && b.noPower) := rfl
@[simp] theorem noPower_div (a b : Expr) : (a/b).noPower = (a.noPower && b.noPower) := rfl
@[simp] theorem noPower_mod (a b : Expr) : (a%b).noPower = (a.noPower && b.noPower) := rfl

end LeanTrominoes.BoundedArithmetic.Expr
