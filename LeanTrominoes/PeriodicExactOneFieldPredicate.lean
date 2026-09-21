/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFFieldTransition
import LeanTrominoes.PeriodicExactOneFieldWindow

/-! # A compiled width-three exact-one window predicate -/
namespace LeanTrominoes.PeriodicCNF.ExactOneFieldPredicate
open BoundedArithmetic BoundedArithmetic.Expr FieldPredicate

/-- The caller has one clause-header binder in front of the saved context. -/
def atomAt (i : Nat) : Expr := existsE (var 1)
  (andE (.testBit (var 4) (var 0))
    (andE (eqE (field 2 (var 0)) (field 2 (var 1+1+.literal (4*i))))
      (.testBit (var 5) (var 0+var 2*phase
        (field 2 (var 1+2+.literal (4*i))) (field 2 (var 1+2))))))

def literalAt (i : Nat) : Expr := orE
  (andE (eqE (field 1 (var 0+4+.literal (4*i))) 1) (atomAt i))
  (andE (eqE (field 1 (var 0+4+.literal (4*i))) 0) (notE (atomAt i)))

def slot (i : Nat) : Expr := .ite (ltE (.literal i) (field 1 (var 0)))
  (.ite (literalAt i) 1 0) 0

def valid : Expr := .all (var 0)
  (impE (.testBit (var 2) (var 0))
    (andE (leE (field 1 (var 0)) 3) (eqE (slot 0+slot 1+slot 2) 1)))

def transition : Expr := andE horizontal (andE localSyntax (andE valid overlap))

theorem transition_noPower : transition.noPower=true := by decide

def slotValue (n : Nat) (truth : Nat → Prop) [DecidablePred truth] (i : Nat) : Nat :=
  if i<n then (decide (truth i)).toNat else 0

instance literalTrueDecidable (n lm word h i : Nat) (fields : List Nat) :
    Decidable (LiteralTrue n lm word h i fields) := by
  unfold LiteralTrue AtomTrue
  infer_instance

def Valid (n cm lm word : Nat) (fields : List Nat) : Prop :=
  ∀ h<n, cm.testBit h=true →
    fields[h]?.getD 0 ≤ 3 ∧
      slotValue (fields[h]?.getD 0) (LiteralTrue n lm word h · fields) 0 +
      slotValue (fields[h]?.getD 0) (LiteralTrue n lm word h · fields) 1 +
      slotValue (fields[h]?.getD 0) (LiteralTrue n lm word h · fields) 2 = 1

@[simp] theorem atomAt_correct (i n cm lm a b h : Nat) (fields : List Nat) :
    (atomAt i).Truth (h::context n cm lm a b fields) ↔
      AtomTrue n lm a (phaseValue (fields[h+2+4*i]?.getD 0) (fields[h+2]?.getD 0))
        (fields[h+1+4*i]?.getD 0) fields := by
  simp only [atomAt,truth_exists,truth_and,truth_bit,truth_eq,eval_add,eval_mul,phase_eval,field_eval2]
  simp [AtomTrue,context,Expr.eval]

@[simp] theorem literalAt_correct (i n cm lm a b h : Nat) (fields : List Nat) :
    (literalAt i).Truth (h::context n cm lm a b fields) ↔ LiteralTrue n lm a h i fields := by
  simp only [literalAt,truth_or,truth_and,truth_eq,truth_not,field_eval1,atomAt_correct]
  simp [LiteralTrue,context,Expr.eval,Op.eval]

@[simp] theorem slot_eval (i n cm lm a b h : Nat) (fields : List Nat) :
    (slot i).eval (h::context n cm lm a b fields) =
      slotValue (fields[h]?.getD 0) (LiteralTrue n lm a h · fields) i := by
  have lit := literalAt_correct i n cm lm a b h fields
  simp only [Truth] at lit
  simp only [slot,Expr.eval,ltE,Op.eval,field_eval1]
  simp only [eval_var,List.getElem?_cons_zero,Option.getD_some,slotValue]
  by_cases hi : i<fields[h]?.getD 0
  · simp only [hi,if_true,ite_false,one_ne_zero]
    by_cases hv : (literalAt i).eval (h::context n cm lm a b fields)=0
    · have no := not_iff_not.mpr lit
      simp [hv,show ¬LiteralTrue n lm a h i fields from no.mp (by simpa using hv)]
    · simp [hv,lit.mp hv]
  · simp [hi]

@[simp] theorem valid_correct (n cm lm a b : Nat) (fields : List Nat) :
    valid.Truth (context n cm lm a b fields) ↔ Valid n cm lm a fields := by
  simp only [valid,truth_all,truth_imp,truth_bit,truth_and,truth_le,truth_eq,
    eval_add,slot_eval,field_eval1]
  simp [Valid,context,Expr.eval]

theorem transition_correct (n cm lm a b : Nat) (fields : List Nat) :
    transition.Truth (context n cm lm a b fields) ↔
      Horizontal n lm fields ∧ Local n cm fields ∧ Valid n cm lm a fields ∧ Overlap n a b := by
  simp [transition]
end LeanTrominoes.PeriodicCNF.ExactOneFieldPredicate
