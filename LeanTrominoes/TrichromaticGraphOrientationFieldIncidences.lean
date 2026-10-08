/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrichromaticGraphOrientationSelectedIndices
import LeanTrominoes.TrichromaticGraphOrientationFieldQueries
import LeanTrominoes.PeriodicThreeDMFieldPredicate

/-! # Arithmetic incidence values read directly from colored graph fields -/
namespace LeanTrominoes.TrichromaticGraphOrientation.FieldPredicate
open FlatEncoding FieldQueries BoundedArithmetic BoundedArithmetic.Expr

def context (n a b : Nat) (values : List Nat) : List Nat := [n,0,0,a,b]++values
def input (graph : Input) (a b : Nat) : List Nat := context graph.2.length a b (fields graph)

def owner (depth : Nat) (index : Expr) : Expr :=
  .ite (index%2) (entry (depth+5) (index/2) 1) (entry (depth+5) (index/2) 0)

def inward (depth : Nat) (index : Expr) : Expr :=
  .ite (index%2)
    (.testBit (var (depth+3)) (index/2+var depth*PeriodicThreeDM.FieldPredicate.phase
      (entry (depth+5) (index/2) 2)))
    (notE (.testBit (var (depth+3)) (index/2+var depth)))

def selected (depth : Nat) (index vertex : Expr) : Expr :=
  andE (eqE (owner depth index) vertex) (inward depth index)

theorem header_eval (graph : Input) (a b : Nat) (front : List Nat) (index : Fin 5) :
    (var (front.length+index.val)).eval (front++input graph a b) =
      [graph.2.length,0,0,a,b][index.val]?.getD 0 := by
  simp only [eval_var,List.getElem?_append_right (by omega : front.length ≤ front.length+index.val),
    Nat.add_sub_cancel_left]
  fin_cases index <;> rfl

theorem owner_eval (graph : Input) (a b : Nat) (front : List Nat) (index : Expr)
    (bound : index.eval (front++input graph a b) < 2*graph.2.length) :
    (owner front.length index).eval (front++input graph a b) =
      (incidenceAt graph (index.eval (front++input graph a b))).1 := by
  let extended := front++[graph.2.length,0,0,a,b]
  have len : extended.length = front.length+5 := by simp [extended]
  have values : extended++fields graph = front++input graph a b := by
    simp [extended,input,context,List.append_assoc]
  have halfBound : (index/2).eval (extended++fields graph) < graph.2.length := by
    rw [values]; change index.eval (front++input graph a b)/2 < graph.2.length; omega
  have source := entry_eval graph extended (index/2) 0 halfBound
  have target := entry_eval graph extended (index/2) 1 halfBound
  simp only [len,values] at source target
  simp only [owner,Expr.eval,Op.eval]
  rw [source,target]
  change (if index.eval (front++input graph a b)%2 = 0 then
    graph.2[index.eval (front++input graph a b)/2].1.source else
    graph.2[index.eval (front++input graph a b)/2].1.target) = _
  simp only [incidenceAt,List.getD_eq_getElem _ _ (by omega :
      index.eval (front++input graph a b)/2 < graph.2.length)]
  split <;> rfl

theorem indexValue_eq (graph : Input) (word index : Nat) (bound : index < 2*graph.2.length) :
    LineWindow.indexValue graph word index =
      if index%2 = 0 then !(word.testBit (index/2+graph.2.length))
      else word.testBit (index/2+graph.2.length*
        ((1-graph.2[index/2].1.offset.1).toNat%3)) := by
  have halfBound : index/2 < graph.2.length := by omega
  simp only [LineWindow.indexValue,incidenceAt,List.getD_eq_getElem _ _ halfBound]
  split <;> simp [LineWindow.assignment,LineWindow.value,LineWindow.decodeWord,LineWindow.position,
    halfBound,finProdFinEquiv,Cell.sub,Int.sub_eq_add_neg,Int.add_comm]

theorem inward_truth (graph : Input) (a b : Nat) (front : List Nat) (index : Expr)
    (bound : index.eval (front++input graph a b) < 2*graph.2.length) :
    (inward front.length index).Truth (front++input graph a b) ↔
      LineWindow.indexValue graph a (index.eval (front++input graph a b)) = true := by
  let extended := front++[graph.2.length,0,0,a,b]
  have len : extended.length = front.length+5 := by simp [extended]
  have values : extended++fields graph = front++input graph a b := by
    simp [extended,input,context,List.append_assoc]
  have halfBound : (index/2).eval (extended++fields graph) < graph.2.length := by
    rw [values]; change index.eval (front++input graph a b)/2 < graph.2.length; omega
  have offset := entry_eval graph extended (index/2) 2 halfBound
  simp only [len,values] at offset
  have count : (var front.length).eval (front++input graph a b) = graph.2.length := by
    simpa using header_eval graph a b front 0
  have word : (var (front.length+3)).eval (front++input graph a b) = a := by
    simpa using header_eval graph a b front 3
  rw [indexValue_eq graph a _ bound]
  unfold inward
  by_cases even : index.eval (front++input graph a b)%2 = 0
  · simp only [Truth,Expr.eval,Op.eval,even,if_true,notE,eqE]
    simp only [count,word]
    change (if (a.testBit (index.eval (front++input graph a b)/2+graph.2.length)).toNat = 0
      then 1 else 0) ≠ 0 ↔ _
    cases a.testBit (index.eval (front++input graph a b)/2+graph.2.length) <;> decide
  · simp only [Truth,Expr.eval,Op.eval,even,if_false]
    rw [count,word]
    change (a.testBit ((index/2).eval (front++input graph a b)+graph.2.length*
      (PeriodicThreeDM.FieldPredicate.phase (entry (front.length+5) (index/2) 2)).eval
        (front++input graph a b))).toNat ≠ 0 ↔ _
    rw [PeriodicThreeDM.FieldPredicate.phase_eval,offset]
    change (a.testBit (index.eval (front++input graph a b)/2+graph.2.length*
      PeriodicThreeDM.FieldPredicate.phaseValue
        (Encodable.encode graph.2[index.eval (front++input graph a b)/2].1.offset.1))).toNat ≠ 0 ↔ _
    rw [PeriodicThreeDM.FieldPredicate.phase_encoded]
    cases a.testBit (index.eval (front++input graph a b)/2+graph.2.length*
      ((1-graph.2[index.eval (front++input graph a b)/2].1.offset.1).toNat%3)) <;> decide

theorem selected_truth (graph : Input) (a b : Nat) (front : List Nat) (index vertex : Expr)
    (bound : index.eval (front++input graph a b) < 2*graph.2.length) :
    (selected front.length index vertex).Truth (front++input graph a b) ↔
      LineWindow.Selected graph (vertex.eval (front++input graph a b)) a
        (index.eval (front++input graph a b)) := by
  simp only [selected,truth_and,truth_eq,owner_eval graph a b front index bound,
    inward_truth graph a b front index bound,LineWindow.Selected]

end LeanTrominoes.TrichromaticGraphOrientation.FieldPredicate
