/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrichromaticGraphOrientationFieldIncidences

/-! # A power-free transition predicate for native colored graph records -/
namespace LeanTrominoes.TrichromaticGraphOrientation.FieldPredicate
open FlatEncoding FieldQueries BoundedArithmetic BoundedArithmetic.Expr
set_option maxHeartbeats 1000000

def kind (depth : Nat) (vertex : Expr) : Expr := .load (.literal (depth+7)+vertex)

theorem kind_eval (graph : Input) (a b : Nat) (front : List Nat) (vertex : Expr)
    (bound : vertex.eval (front++input graph a b) < graph.1.length) :
    (kind front.length vertex).eval (front++input graph a b) =
      (graph.1.getD (vertex.eval (front++input graph a b)) false).toNat := by
  let index := vertex.eval (front++input graph a b)
  change (front++input graph a b)[front.length+7+index]?.getD 0 = _
  rw [List.getElem?_append_right (by omega)]
  have address : front.length+7+index-front.length = index+7 := by omega
  rw [address]
  change ((graph.1.map Bool.toNat ++ graph.2.flatMap edgeFields)[index]?).getD 0 = _
  rw [List.getElem?_append_left (by simpa [index] using bound)]
  simp [index,List.getElem?_map,List.getElem?_eq_getElem bound]

theorem inward_eval (graph : Input) (a b : Nat) (front : List Nat) (index : Expr)
    (bound : index.eval (front++input graph a b) < 2*graph.2.length) :
    (inward front.length index).eval (front++input graph a b) =
      (LineWindow.indexValue graph a (index.eval (front++input graph a b))).toNat := by
  have correct := inward_truth graph a b front index bound
  have small : (inward front.length index).eval (front++input graph a b) ≤ 1 := by
    simp only [inward,Expr.eval,Op.eval,notE,eqE]
    split
    · split <;> omega
    · exact Bool.toNat_le _
  unfold Truth at correct
  cases value : LineWindow.indexValue graph a (index.eval (front++input graph a b)) <;>
    simp [value] at correct ⊢ <;> omega

def coherent : Expr := .all (2*var 1)
  (impE (eqE (owner 2 (var 0)) (var 1))
    (.all (2*var 2) (impE (eqE (owner 3 (var 0)) (var 2))
      (eqE (inward 3 (var 1)) (inward 3 (var 0))))))

def exactOne : Expr := existsE (2*var 1)
  (andE (selected 2 (var 0) (var 1))
    (.all (2*var 2) (impE (selected 3 (var 0) (var 2)) (eqE (var 0) (var 1)))))

def valid : Expr := .all (var 5) (.ite (kind 1 (var 0)) coherent exactOne)
def overlap : Expr := PeriodicCNF.FieldPredicate.overlap
def transition : Expr := andE valid overlap
def decision : Expr := .ite transition 1 0
def check (graph : Input) (a b : Nat) : Bool := decide (transition.eval (input graph a b) ≠ 0)

theorem coherent_typed (graph : Input) (a b vertex : Nat) :
    coherent.Truth (vertex::input graph a b) ↔
      Coherent (LineWindow.assignment graph (LineWindow.decodeWord graph a)) (0,0) (incoming graph vertex) := by
  rw [LineWindow.coherent_iff_indices]
  simp only [coherent,truth_all,truth_imp,truth_eq]
  change (∀ first < 2*graph.2.length,
    (owner 2 (var 0)).eval (first::vertex::input graph a b) = vertex →
    ∀ second < 2*graph.2.length,
      (owner 3 (var 0)).eval (second::first::vertex::input graph a b) = vertex →
      (inward 3 (var 1)).eval (second::first::vertex::input graph a b) =
        (inward 3 (var 0)).eval (second::first::vertex::input graph a b)) ↔ _
  apply forall_congr'; intro first
  apply forall_congr'; intro firstBound
  have firstOwner := owner_eval graph a b [first,vertex] (var 0) firstBound
  change (owner 2 (var 0)).eval (first::vertex::input graph a b) = (incidenceAt graph first).1 at firstOwner
  rw [firstOwner]
  apply imp_congr_right; intro _
  apply forall_congr'; intro second
  apply forall_congr'; intro secondBound
  have secondOwner := owner_eval graph a b [second,first,vertex] (var 0) secondBound
  change (owner 3 (var 0)).eval (second::first::vertex::input graph a b) = (incidenceAt graph second).1 at secondOwner
  have firstValue := inward_eval graph a b [second,first,vertex] (var 1) firstBound
  change (inward 3 (var 1)).eval (second::first::vertex::input graph a b) =
    (LineWindow.indexValue graph a first).toNat at firstValue
  have secondValue := inward_eval graph a b [second,first,vertex] (var 0) secondBound
  change (inward 3 (var 0)).eval (second::first::vertex::input graph a b) =
    (LineWindow.indexValue graph a second).toNat at secondValue
  rw [secondOwner,firstValue,secondValue]
  have boolEq (first second : Bool) : first.toNat = second.toNat ↔ first = second := by
    cases first <;> cases second <;> decide
  simp only [boolEq]

theorem exactOne_typed (graph : Input) (a b vertex : Nat) :
    exactOne.Truth (vertex::input graph a b) ↔
      PeriodicOneInThree.ClauseHolds (LineWindow.assignment graph (LineWindow.decodeWord graph a))
        (0,0) (incoming graph vertex) := by
  rw [LineWindow.exactlyOne_iff_unique]
  simp only [exactOne,truth_exists,truth_and,truth_all,truth_imp,truth_eq]
  change (∃ first < 2*graph.2.length,
    (selected 2 (var 0) (var 1)).Truth (first::vertex::input graph a b) ∧
    ∀ second < 2*graph.2.length,
      (selected 3 (var 0) (var 2)).Truth (second::first::vertex::input graph a b) → second=first) ↔ _
  apply exists_congr; intro first
  apply and_congr_right; intro firstBound
  have firstSelected := selected_truth graph a b [first,vertex] (var 0) (var 1) firstBound
  change (selected 2 (var 0) (var 1)).Truth (first::vertex::input graph a b) ↔
    LineWindow.Selected graph vertex a first at firstSelected
  rw [firstSelected]
  apply and_congr_right; intro _
  apply forall_congr'; intro second
  apply forall_congr'; intro secondBound
  have secondSelected := selected_truth graph a b [second,first,vertex] (var 0) (var 2) secondBound
  change (selected 3 (var 0) (var 2)).Truth (second::first::vertex::input graph a b) ↔
    LineWindow.Selected graph vertex a second at secondSelected
  rw [secondSelected]

theorem valid_typed (graph : Input) (a b : Nat) :
    valid.Truth (input graph a b) ↔ LineWindow.Valid graph (LineWindow.decodeWord graph a) := by
  rw [valid,truth_all]
  change (∀ vertex < graph.1.length,
    (Expr.ite (kind 1 (var 0)) coherent exactOne).Truth (vertex::input graph a b)) ↔ _
  apply forall_congr'; intro vertex
  apply forall_congr'; intro bound
  have kindAt := kind_eval graph a b [vertex] (var 0) bound
  change (kind 1 (var 0)).eval (vertex::input graph a b) = (graph.1.getD vertex false).toNat at kindAt
  cases isTri : graph.1.getD vertex false
  · simpa only [Truth,Expr.eval,kindAt,isTri,Bool.toNat_false,ite_true,Bool.false_eq_true,ite_false]
      using exactOne_typed graph a b vertex
  · simpa only [Truth,Expr.eval,kindAt,isTri,Bool.toNat_true,Nat.one_ne_zero,ite_false,ite_true]
      using coherent_typed graph a b vertex

theorem overlap_typed (graph : Input) (a b : Nat) :
    overlap.Truth (input graph a b) ↔ ∀ column : Fin 2,
      LineWindow.decodeWord graph a column.succ = LineWindow.decodeWord graph b column.castSucc := by
  change PeriodicCNF.FieldPredicate.overlap.Truth
    (PeriodicCNF.FieldPredicate.context graph.2.length 0 0 a b (fields graph)) ↔ _
  rw [PeriodicCNF.FieldPredicate.overlap_correct]
  constructor
  · intro raw column
    funext edge
    fin_cases column
    · change a.testBit (edge.val+graph.2.length*1) = b.testBit (edge.val+graph.2.length*0)
      simpa using (raw edge.val edge.isLt).1
    · change a.testBit (edge.val+graph.2.length*2) = b.testBit (edge.val+graph.2.length*1)
      simpa using (raw edge.val edge.isLt).2
  · intro typed edge bound
    have first := congrFun (typed 0) ⟨edge,bound⟩
    have second := congrFun (typed 1) ⟨edge,bound⟩
    change a.testBit (edge+graph.2.length*1) = b.testBit (edge+graph.2.length*0) at first
    change a.testBit (edge+graph.2.length*2) = b.testBit (edge+graph.2.length*1) at second
    simpa [PeriodicCNF.FieldPredicate.Overlap] using And.intro first second

theorem transition_typed (graph : Input) (a b : Nat) :
    transition.Truth (input graph a b) ↔ LineWindow.packedTransition graph a b := by
  rw [transition,truth_and,valid_typed,overlap_typed]
  rfl

theorem check_true (graph : Input) (a b : Nat) :
    check graph a b = true ↔ LineWindow.packedTransition graph a b := by
  simpa only [check,decide_eq_true_eq,Truth] using transition_typed graph a b

theorem transition_noPower : transition.noPower = true := by
  simp [transition,valid,coherent,exactOne,selected,inward,owner,kind,entry,
    PeriodicThreeDM.FieldPredicate.phase,overlap,PeriodicCNF.FieldPredicate.overlap,
    existsE,notE,eqE,andE,impE,var,Expr.noPower]

theorem decision_noPower : decision.noPower = true := by simp [decision,Expr.noPower,transition_noPower]

theorem decision_eval (graph : Input) (a b : Nat) :
    decision.eval (input graph a b) = (check graph a b).toNat := by
  by_cases zero : transition.eval (input graph a b)=0 <;> simp [decision,Expr.eval,check,zero]

theorem cycle_iff (graph : Input) (horizontal : IsOneDimensional graph) (locality : IsLocal graph) :
    FiniteState.HasCycle (fun a b : LineWindow.PackedState graph => check graph a.val b.val=true) ↔
      HasOrientation graph := by
  rw [LineWindow.hasOrientation_iff_packed_cycle graph horizontal locality]
  constructor
  · rintro ⟨period,states,steps⟩
    exact ⟨period,states,fun index => (check_true graph _ _).mp (steps index)⟩
  · rintro ⟨period,states,steps⟩
    exact ⟨period,states,fun index => (check_true graph _ _).mpr (steps index)⟩

end LeanTrominoes.TrichromaticGraphOrientation.FieldPredicate
