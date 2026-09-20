/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BoundedArithmeticLogic
import LeanTrominoes.PartrecIntOffset

/-! # A power-free compiled transition predicate over flat CNF fields -/
namespace LeanTrominoes.PeriodicCNF.FieldPredicate
open BoundedArithmetic BoundedArithmetic.Expr Turing.ToPartrec

def field (depth : Nat) (index : Expr) : Expr := .load (index+.literal (5+depth))
def successor (a : Expr) : Expr := .ite (a%2) (a-2) (a+2)
def phase (a anchor : Expr) : Expr := .ite (eqE a anchor) 1 (.ite (eqE a (successor anchor)) 2 0)
def nearby (a b : Expr) : Expr := orE (eqE a b) (orE (eqE a (successor b)) (eqE b (successor a)))

def phaseValue (a anchor : Nat) : Nat :=
  if a=anchor then 1 else if a=Code.intCodeSuccessor anchor then 2 else 0

theorem successor_eval (a : Expr) (v : List Nat) :
    (successor a).eval v = Code.intCodeSuccessor (a.eval v) := by
  change (if a.eval v % 2 = 0 then a.eval v+2 else a.eval v-2) = _
  rw [Nat.mod_two_of_bodd]
  cases h : (a.eval v).bodd <;> simp [Code.intCodeSuccessor,h]

theorem phase_eval (a b : Expr) (v : List Nat) :
    (phase a b).eval v = phaseValue (a.eval v) (b.eval v) := by
  simp [phase,phaseValue,Expr.eval,eqE,Op.eval,successor_eval]

def atomTruth : Expr := existsE (var 2)
  (andE (.testBit (var 5) (var 0))
    (andE (eqE (field 3 (var 0)) (field 3 (var 2+1+4*var 1)))
      (.testBit (var 6) (var 0+var 3*phase
        (field 3 (var 2+2+4*var 1)) (field 3 (var 2+2))))))

def literalTruth : Expr := orE
  (andE (eqE (field 2 (var 1+4+4*var 0)) 1) atomTruth)
  (andE (eqE (field 2 (var 1+4+4*var 0)) 0) (notE atomTruth))

def valid : Expr := .all (var 0)
  (impE (.testBit (var 2) (var 0)) (existsE (field 1 (var 0)) literalTruth))

def horizontal : Expr := .all (var 0)
  (impE (.testBit (var 3) (var 0)) (eqE (field 1 (var 0+2)) 0))

def localSyntax : Expr := .all (var 0)
  (impE (.testBit (var 2) (var 0))
    (.all (field 1 (var 0)) (.all (field 2 (var 1))
      (nearby (field 3 (var 2+2+4*var 1)) (field 3 (var 2+2+4*var 0))))))

def overlap : Expr := .all (var 0)
  (andE (eqE (.testBit (var 4) (var 0+var 1)) (.testBit (var 5) (var 0)))
    (eqE (.testBit (var 4) (var 0+var 1*2)) (.testBit (var 5) (var 0+var 1))))

def transition : Expr := andE horizontal (andE localSyntax (andE valid overlap))

theorem transition_noPower : transition.noPower = true := by decide

def context (n cm lm first second : Nat) (fields : List Nat) : List Nat :=
  [n,cm,lm,first,second]++fields

def AtomTrue (n lm word column atom : Nat) (fields : List Nat) : Prop :=
  ∃ p<n, lm.testBit p = true ∧ fields[p]?.getD 0 = atom ∧ word.testBit (p+n*column) = true

def LiteralTrue (n lm word header index : Nat) (fields : List Nat) : Prop :=
  let atom := fields[header+1+4*index]?.getD 0
  let col := phaseValue (fields[header+2+4*index]?.getD 0) (fields[header+2]?.getD 0)
  (fields[header+4+4*index]?.getD 0 = 1 ∧ AtomTrue n lm word col atom fields) ∨
  (fields[header+4+4*index]?.getD 0 = 0 ∧ ¬AtomTrue n lm word col atom fields)

def Valid (n cm lm word : Nat) (fields : List Nat) : Prop :=
  ∀ h<n, cm.testBit h = true → ∃ k<fields[h]?.getD 0, LiteralTrue n lm word h k fields

def Horizontal (n lm : Nat) (fields : List Nat) : Prop :=
  ∀ p<n, lm.testBit p = true → fields[p+2]?.getD 0 = 0

def Local (n cm : Nat) (fields : List Nat) : Prop :=
  ∀ h<n, cm.testBit h = true → ∀ k<fields[h]?.getD 0, ∀ j<fields[h]?.getD 0,
    let a := fields[h+2+4*k]?.getD 0
    let b := fields[h+2+4*j]?.getD 0
    a=b ∨ a=Code.intCodeSuccessor b ∨ b=Code.intCodeSuccessor a

def Overlap (n first second : Nat) : Prop :=
  ∀ p<n, first.testBit (p+n) = second.testBit p ∧
    first.testBit (p+n*2) = second.testBit (p+n)

theorem field_eval (d : Nat) (i : Expr) (front fields : List Nat) (hp : front.length=5+d) :
    (field d i).eval (front++fields) = fields[i.eval (front++fields)]?.getD 0 := by
  simp only [field,Expr.eval,Op.eval]
  rw [List.getElem?_append_right (by omega)]
  congr 2
  omega

@[simp] theorem field_eval0 (i : Expr) (n cm lm a b : Nat) (fields : List Nat) :
    (field 0 i).eval (context n cm lm a b fields) =
      fields[i.eval (context n cm lm a b fields)]?.getD 0 :=
  field_eval 0 i [n,cm,lm,a,b] fields rfl

@[simp] theorem field_eval1 (i : Expr) (x n cm lm a b : Nat) (fields : List Nat) :
    (field 1 i).eval (x::context n cm lm a b fields) =
      fields[i.eval (x::context n cm lm a b fields)]?.getD 0 :=
  field_eval 1 i [x,n,cm,lm,a,b] fields rfl

@[simp] theorem field_eval2 (i : Expr) (x y n cm lm a b : Nat) (fields : List Nat) :
    (field 2 i).eval (x::y::context n cm lm a b fields) =
      fields[i.eval (x::y::context n cm lm a b fields)]?.getD 0 :=
  field_eval 2 i [x,y,n,cm,lm,a,b] fields rfl

@[simp] theorem field_eval3 (i : Expr) (x y z n cm lm a b : Nat) (fields : List Nat) :
    (field 3 i).eval (x::y::z::context n cm lm a b fields) =
      fields[i.eval (x::y::z::context n cm lm a b fields)]?.getD 0 :=
  field_eval 3 i [x,y,z,n,cm,lm,a,b] fields rfl

@[simp] theorem atomTruth_correct (n cm lm a b h k : Nat) (fields : List Nat) :
    atomTruth.Truth (k::h::context n cm lm a b fields) ↔
      AtomTrue n lm a (phaseValue (fields[h+2+4*k]?.getD 0) (fields[h+2]?.getD 0))
        (fields[h+1+4*k]?.getD 0) fields := by
  simp only [atomTruth,truth_exists,truth_and,truth_bit,truth_eq,eval_add,eval_mul,phase_eval,field_eval3]
  simp [AtomTrue,context,Expr.eval,Op.eval]

@[simp] theorem literalTruth_correct (n cm lm a b h k : Nat) (fields : List Nat) :
    literalTruth.Truth (k::h::context n cm lm a b fields) ↔ LiteralTrue n lm a h k fields := by
  simp only [literalTruth,truth_or,truth_and,truth_eq,truth_not,field_eval2,atomTruth_correct]
  simp [LiteralTrue,context,Expr.eval,Op.eval]

@[simp] theorem valid_correct (n cm lm a b : Nat) (fields : List Nat) :
    valid.Truth (context n cm lm a b fields) ↔ Valid n cm lm a fields := by
  simp only [valid,truth_all,truth_imp,truth_bit,truth_exists,field_eval1,literalTruth_correct]
  simp [Valid,context,Expr.eval]

@[simp] theorem horizontal_correct (n cm lm a b : Nat) (fields : List Nat) :
    horizontal.Truth (context n cm lm a b fields) ↔ Horizontal n lm fields := by
  simp only [horizontal,truth_all,truth_imp,truth_bit,truth_eq,field_eval1]
  simp [Horizontal,context,Expr.eval,Op.eval]

@[simp] theorem localSyntax_correct (n cm lm a b : Nat) (fields : List Nat) :
    localSyntax.Truth (context n cm lm a b fields) ↔ Local n cm fields := by
  simp only [localSyntax,truth_all,truth_imp,truth_bit,nearby,truth_or,truth_eq,
    successor_eval,field_eval1,field_eval2,field_eval3]
  simp [Local,context,Expr.eval,Op.eval]

private theorem bool_nat_eq (a b : Bool) : a.toNat=b.toNat ↔ a=b := by cases a <;> cases b <;> decide

@[simp] theorem overlap_correct (n cm lm a b : Nat) (fields : List Nat) :
    overlap.Truth (context n cm lm a b fields) ↔ Overlap n a b := by
  simp only [overlap,truth_all,truth_and,truth_eq]
  simp [Overlap,context,Expr.eval,Op.eval,bool_nat_eq]

theorem transition_correct (n cm lm a b : Nat) (fields : List Nat) :
    transition.Truth (context n cm lm a b fields) ↔
      Horizontal n lm fields ∧ Local n cm fields ∧ Valid n cm lm a fields ∧ Overlap n a b := by
  simp [transition]

/-- The actual evaluator program for the transition test has linear space
in its flat input, including the two binary state words. -/
theorem transition_fits (v : List Nat) :
    Turing.PartrecToTM2.EvaluatorCodeFits transition.code v [transition.eval v]
      ((transition.weight*(transition.radius+1))*(Turing.PartrecToTM2.encodedListSpace v+1)) :=
  transition.code_fits_automatic v transition_noPower

end LeanTrominoes.PeriodicCNF.FieldPredicate
