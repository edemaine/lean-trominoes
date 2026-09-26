/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeDMSelectedIndices
import LeanTrominoes.PeriodicThreeDMFieldQueries
import LeanTrominoes.PeriodicCNFFieldPredicate

/-! # Power-free arithmetic for the three-column matching predicate -/
namespace LeanTrominoes.PeriodicThreeDM.FieldPredicate
open Gadget FlatEncoding FieldQueries BoundedArithmetic BoundedArithmetic.Expr

def context (n a b : Nat) (values : List Nat) : List Nat := [n,0,0,a,b]++values
def input (p : PeriodicThreeDM) (a b : Nat) : List Nat := context p.triples.length a b (fields p)

def phaseValue (code : Nat) : Nat :=
  if code%2=0 then (1-code/2)%3 else (code/2+2)%3

def phase (q : Expr) : Expr := .ite (q%2) ((q/2+2)%3) ((1-q/2)%3)

theorem phase_eval (q : Expr) (values : List Nat) : (phase q).eval values = phaseValue (q.eval values) := rfl

theorem phase_encoded (z : Int) : phaseValue (Encodable.encode z) = (1-z).toNat%3 := by
  cases z with
  | ofNat n =>
    change phaseValue (2*n) = (1-(n:Int)).toNat%3
    have h : (1-(n:Int)).toNat = 1-n := by omega
    simp [phaseValue,h]
  | negSucc n =>
    change phaseValue (2*n+1) = (1-Int.negSucc n).toNat%3
    have h : (1-Int.negSucc n).toNat = n+2 := by omega
    simp [phaseValue,h,Nat.add_div]

def selected (depth : Nat) (color : WireColor) (index atom : Expr) : Expr :=
  andE (eqE (entry (depth+5) index color 0) atom)
    (.testBit (var (depth+3)) (index+var depth*phase (entry (depth+5) index color 1)))

theorem selected_truth (p : PeriodicThreeDM) (a b : Nat) (front : List Nat)
    (color : WireColor) (index atom : Expr)
    (hi : index.eval (front++input p a b) < p.triples.length) :
    (selected front.length color index atom).Truth (front++input p a b) ↔
      LineWindow.Selected p color (atom.eval (front++input p a b)) a (index.eval (front++input p a b)) := by
  let extended := front++[p.triples.length,0,0,a,b]
  have len : extended.length = front.length+5 := by simp [extended]
  have values : extended++fields p = front++input p a b := by simp [extended,input,context,List.append_assoc]
  have atomAt := entry_eval p extended index color 0 (by simpa only [values] using hi)
  have offsetAt := entry_eval p extended index color 1 (by simpa only [values] using hi)
  simp only [len,values] at atomAt offsetAt
  simp only [selected,truth_and,truth_eq,truth_bit,eval_add,eval_mul,phase_eval]
  rw [atomAt,offsetAt]
  have header (i : Fin 5) : (var (front.length+i.val)).eval (front++input p a b) =
      [p.triples.length,0,0,a,b][i.val]?.getD 0 := by
    simp only [eval_var,List.getElem?_append_right (by omega : front.length ≤ front.length+i.val),Nat.add_sub_cancel_left]
    fin_cases i <;> rfl
  have count : (var front.length).eval (front++input p a b) = p.triples.length := by simpa using header 0
  have word : (var (front.length+3)).eval (front++input p a b) = a := by simpa using header 3
  rw [count,word]
  simp only [referenceFields,Fin.val_zero,Fin.val_one,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  rw [phase_encoded]
  simp only [LineWindow.Selected,incidentIndex,LineWindow.indexValue,LineWindow.position,List.getD_eq_getElem _ _ hi]

def colorValid (color : WireColor) : Expr := .all (var (5+colorIndex color))
  (existsE (var 1) (andE (selected 2 color (var 0) (var 1))
    (.all (var 2) (impE (selected 3 color (var 0) (var 2)) (eqE (var 0) (var 1))))))

def valid : Expr := andE (colorValid .red) (andE (colorValid .green) (colorValid .blue))
def overlap : Expr := PeriodicCNF.FieldPredicate.overlap
def transition : Expr := andE valid overlap

theorem transition_noPower : transition.noPower = true := by
  simp [transition,valid,colorValid,selected,phase,entry,overlap,PeriodicCNF.FieldPredicate.overlap,
    existsE,notE,eqE,andE,impE,var,Expr.noPower]

def check (p : PeriodicThreeDM) (a b : Nat) : Bool := decide (transition.eval (input p a b) ≠ 0)
def decision : Expr := .ite transition 1 0

theorem decision_noPower : decision.noPower = true := by simp [decision,Expr.noPower,transition_noPower]

theorem decision_eval (p : PeriodicThreeDM) (a b : Nat) : decision.eval (input p a b) = (check p a b).toNat := by
  by_cases h : transition.eval (input p a b)=0 <;> simp [decision,Expr.eval,check,h]

end LeanTrominoes.PeriodicThreeDM.FieldPredicate
