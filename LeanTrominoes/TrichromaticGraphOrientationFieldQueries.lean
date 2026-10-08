/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrichromaticGraphOrientationFlatEncoding
import LeanTrominoes.BoundedArithmeticLogic

/-! # Direct arithmetic queries of colored graph input records -/
namespace LeanTrominoes.TrichromaticGraphOrientation.FieldQueries
open Gadget FlatEncoding BoundedArithmetic BoundedArithmetic.Expr

private theorem edge_get (records : List (PeriodicEdge Nat × WireColor)) (index : Nat) (field : Fin 5)
    (bound : index < records.length) :
    (records.flatMap edgeFields)[5*index+field.val]?.getD 0 = (edgeFields records[index])[field.val]?.getD 0 := by
  induction records generalizing index with
  | nil => simp at bound
  | cons record records ih =>
    cases index with
    | zero => fin_cases field <;> simp [edgeFields]
    | succ index =>
      have equality := ih index (by simpa using bound)
      have address : 5*(index+1)+field.val = (5*index+field.val)+1+1+1+1+1 := by omega
      simpa [edgeFields,address] using equality

def entry (depth : Nat) (index : Expr) (field : Fin 5) : Expr :=
  .load (.literal (depth+2)+var depth+5*index+.literal field.val)

theorem vertexCount_eval (input : Input) (front : List Nat) :
    (var front.length).eval (front++fields input) = input.1.length := by
  simp [eval_var,fields]

theorem edgeCount_eval (input : Input) (front : List Nat) :
    (var (front.length+1)).eval (front++fields input) = input.2.length := by
  simp [eval_var,fields]

theorem entry_eval (input : Input) (front : List Nat) (index : Expr) (field : Fin 5)
    (bound : index.eval (front++fields input) < input.2.length) :
    (entry front.length index field).eval (front++fields input) =
      (edgeFields input.2[index.eval (front++fields input)])[field.val]?.getD 0 := by
  let i := index.eval (front++fields input)
  change ((front++fields input)[front.length+2+(var front.length).eval (front++fields input)+5*i+field.val]?).getD 0 = _
  rw [vertexCount_eval]
  rw [List.getElem?_append_right (by omega)]
  have address : front.length+2+input.1.length+5*i+field.val-front.length =
      (input.1.length+(5*i+field.val))+1+1 := by omega
  rw [address]
  simp only [fields,List.getElem?_cons_succ]
  rw [List.getElem?_append_right (by simp)]
  simp only [List.length_map,Nat.add_sub_cancel_left]
  exact edge_get input.2 i field bound

theorem entry_noPower (depth : Nat) (index : Expr) (field : Fin 5) (allowed : index.noPower = true) :
    (entry depth index field).noPower = true := by
  simp [entry,Expr.noPower,allowed,var]

end LeanTrominoes.TrichromaticGraphOrientation.FieldQueries
