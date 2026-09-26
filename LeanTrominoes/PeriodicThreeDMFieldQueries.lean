/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeDMFlatEncoding
import LeanTrominoes.BoundedArithmeticLogic

/-! # Direct arithmetic queries of native periodic 3DM fields -/
namespace LeanTrominoes.PeriodicThreeDM.FieldQueries
open Gadget FlatEncoding BoundedArithmetic BoundedArithmetic.Expr

def colorIndex : WireColor → Nat
  | .red => 0
  | .green => 1
  | .blue => 2

private theorem triple_get (ts : List PeriodicThreeDMTriple) (i : Nat) (field : Fin 9)
    (hi : i < ts.length) :
    (ts.flatMap tripleFields)[9*i+field.val]?.getD 0 =
      (tripleFields ts[i])[field.val]?.getD 0 := by
  induction ts generalizing i with
  | nil => simp at hi
  | cons t ts ih =>
    cases i with
    | zero => fin_cases field <;> simp [tripleFields,referenceFields]
    | succ i =>
      have h := ih i (by simpa using hi)
      have address : 9*(i+1)+field.val = (9*i+field.val)+1+1+1+1+1+1+1+1+1 := by omega
      simpa [tripleFields,referenceFields,address] using h

def entry (depth : Nat) (index : Expr) (color : WireColor) (field : Fin 3) : Expr :=
  .load (.literal (depth+4)+9*index+.literal (3*colorIndex color+field.val))

theorem entry_eval (p : PeriodicThreeDM) (front : List Nat) (index : Expr)
    (color : WireColor) (field : Fin 3)
    (hi : index.eval (front++fields p) < p.triples.length) :
    (entry front.length index color field).eval (front++fields p) =
      (referenceFields (p.triples[index.eval (front++fields p)].reference color))[field.val]?.getD 0 := by
  let i := index.eval (front++fields p)
  change ((front++fields p)[front.length+4+9*i+(3*colorIndex color+field.val)]?).getD 0 = _
  rw [List.getElem?_append_right (by omega)]
  have address : front.length+4+9*i+(3*colorIndex color+field.val)-front.length =
      (9*i+(3*colorIndex color+field.val))+1+1+1+1 := by omega
  rw [address]
  simp only [fields,List.getElem?_cons_succ]
  have valid : 3*colorIndex color+field.val < 9 := by cases color <;> simp only [colorIndex] <;> omega
  rw [triple_get p.triples i ⟨3*colorIndex color+field.val,valid⟩ hi]
  cases color <;> fin_cases field <;> rfl

theorem entry_noPower (depth : Nat) (index : Expr) (color : WireColor) (field : Fin 3)
    (allowed : index.noPower = true) : (entry depth index color field).noPower = true := by
  simp [entry,Expr.noPower,allowed]

theorem count_eval (p : PeriodicThreeDM) (front : List Nat) (color : WireColor) :
    (var (front.length+colorIndex color)).eval (front++fields p) = p.elementCount color := by
  simp only [eval_var,List.getElem?_append_right (by omega : front.length ≤ front.length+colorIndex color),Nat.add_sub_cancel_left]
  cases color <;> rfl

end LeanTrominoes.PeriodicThreeDM.FieldQueries
