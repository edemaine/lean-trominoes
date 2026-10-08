/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrichromaticGraphOrientationFieldTransition
import LeanTrominoes.TrichromaticGraphOrientationIncidenceCounts

/-! # Arithmetic degree and color checks for native orientation instances -/
namespace LeanTrominoes.TrichromaticGraphOrientation.VertexGuard
open Gadget FlatEncoding FieldQueries FieldPredicate BoundedArithmetic BoundedArithmetic.Expr
set_option maxHeartbeats 1000000

def ownerMatch (depth : Nat) (index vertex : Expr) : Expr := eqE (owner depth index) vertex
def colorAt (depth : Nat) (index : Expr) : Expr := entry (depth+5) (index/2) 4
def colored (depth : Nat) (index vertex : Expr) (color : WireColor) : Expr :=
  andE (ownerMatch depth index vertex) (eqE (colorAt depth index) (.literal (colorField color)))

theorem ownerMatch_truth (graph : Input) (front : List Nat) (index vertex : Expr)
    (bound : index.eval (front++input graph 0 0) < 2*graph.2.length) :
    (ownerMatch front.length index vertex).Truth (front++input graph 0 0) ↔
      (incidenceAt graph (index.eval (front++input graph 0 0))).1 = vertex.eval (front++input graph 0 0) := by
  rw [ownerMatch,truth_eq,owner_eval graph 0 0 front index bound]

theorem colorAt_eval (graph : Input) (front : List Nat) (index : Expr)
    (bound : index.eval (front++input graph 0 0) < 2*graph.2.length) :
    (colorAt front.length index).eval (front++input graph 0 0) =
      colorField (incidenceAt graph (index.eval (front++input graph 0 0))).2.2 := by
  let extended := front++[graph.2.length,0,0,0,0]
  have len : extended.length = front.length+5 := by simp [extended]
  have values : extended++fields graph = front++input graph 0 0 := by
    simp [extended,input,context,List.append_assoc]
  have halfBound : (index/2).eval (extended++fields graph) < graph.2.length := by
    rw [values]; change index.eval (front++input graph 0 0)/2 < graph.2.length; omega
  have field := entry_eval graph extended (index/2) 4 halfBound
  simp only [len,values] at field
  rw [colorAt,field]
  change colorField graph.2[index.eval (front++input graph 0 0)/2].2 = _
  simp only [incidenceAt,List.getD_eq_getElem _ _ (by omega :
    index.eval (front++input graph 0 0)/2 < graph.2.length)]
  split <;> rfl

private theorem colorField_injective : Function.Injective colorField := by
  intro first second equal
  cases first <;> cases second <;> simp_all [colorField]

theorem colored_truth (graph : Input) (front : List Nat) (index vertex : Expr) (color : WireColor)
    (bound : index.eval (front++input graph 0 0) < 2*graph.2.length) :
    (colored front.length index vertex color).Truth (front++input graph 0 0) ↔
      (incidenceAt graph (index.eval (front++input graph 0 0))).1 = vertex.eval (front++input graph 0 0) ∧
        (incidenceAt graph (index.eval (front++input graph 0 0))).2.2 = color := by
  simp only [colored,truth_and,ownerMatch_truth graph front index vertex bound,truth_eq,
    colorAt_eval graph front index bound,eval_literal,colorField_injective.eq_iff]

-- Context: third, second, first, vertex, then the saved input.
def witnesses : Expr := andE (notE (eqE (var 2) (var 1)))
  (andE (notE (eqE (var 2) (var 0))) (andE (notE (eqE (var 1) (var 0)))
    (andE (ownerMatch 4 (var 2) (var 3)) (andE (ownerMatch 4 (var 1) (var 3))
      (andE (ownerMatch 4 (var 0) (var 3))
        (.all (2*var 4) (impE (ownerMatch 5 (var 0) (var 4))
          (orE (eqE (var 0) (var 3)) (orE (eqE (var 0) (var 2)) (eqE (var 0) (var 1)))))))))))

def degree : Expr := existsE (2*var 1) (existsE (2*var 2) (existsE (2*var 3) witnesses))

theorem witnesses_truth (graph : Input) (vertex first second third : Nat)
    (firstBound : first < 2*graph.2.length) (secondBound : second < 2*graph.2.length)
    (thirdBound : third < 2*graph.2.length) :
    witnesses.Truth (third::second::first::vertex::input graph 0 0) ↔
      first ≠ second ∧ first ≠ third ∧ second ≠ third ∧
      (incidenceAt graph first).1 = vertex ∧ (incidenceAt graph second).1 = vertex ∧
      (incidenceAt graph third).1 = vertex ∧
      ∀ index < 2*graph.2.length, (incidenceAt graph index).1 = vertex →
        index = first ∨ index = second ∨ index = third := by
  have firstAt := ownerMatch_truth graph [third,second,first,vertex] (var 2) (var 3) firstBound
  have secondAt := ownerMatch_truth graph [third,second,first,vertex] (var 1) (var 3) secondBound
  have thirdAt := ownerMatch_truth graph [third,second,first,vertex] (var 0) (var 3) thirdBound
  change (ownerMatch 4 (var 2) (var 3)).Truth (third::second::first::vertex::input graph 0 0) ↔
    (incidenceAt graph first).1 = vertex at firstAt
  change (ownerMatch 4 (var 1) (var 3)).Truth (third::second::first::vertex::input graph 0 0) ↔
    (incidenceAt graph second).1 = vertex at secondAt
  change (ownerMatch 4 (var 0) (var 3)).Truth (third::second::first::vertex::input graph 0 0) ↔
    (incidenceAt graph third).1 = vertex at thirdAt
  simp only [witnesses,truth_and,truth_not,truth_eq,truth_all,truth_imp,truth_or,firstAt,secondAt,thirdAt]
  change (first ≠ second ∧ first ≠ third ∧ second ≠ third ∧
    (incidenceAt graph first).1 = vertex ∧ (incidenceAt graph second).1 = vertex ∧
    (incidenceAt graph third).1 = vertex ∧ ∀ index < 2*graph.2.length,
      (ownerMatch 5 (var 0) (var 4)).Truth (index::third::second::first::vertex::input graph 0 0) →
        index = first ∨ index = second ∨ index = third) ↔ _
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  apply forall_congr'; intro index
  apply forall_congr'; intro bound
  have atIndex := ownerMatch_truth graph [index,third,second,first,vertex] (var 0) (var 4) bound
  change (ownerMatch 5 (var 0) (var 4)).Truth (index::third::second::first::vertex::input graph 0 0) ↔
    (incidenceAt graph index).1 = vertex at atIndex
  rw [atIndex]

theorem degree_truth (graph : Input) (vertex : Nat) : degree.Truth (vertex::input graph 0 0) ↔
    (colors graph vertex).length = 3 := by
  rw [degree_three_iff]
  simp only [degree,truth_exists]
  change (∃ first < 2*graph.2.length, ∃ second < 2*graph.2.length, ∃ third < 2*graph.2.length,
    witnesses.Truth (third::second::first::vertex::input graph 0 0)) ↔ _
  apply exists_congr; intro first
  apply and_congr_right; intro firstBound
  apply exists_congr; intro second
  apply and_congr_right; intro secondBound
  apply exists_congr; intro third
  apply and_congr_right; intro thirdBound
  exact witnesses_truth graph vertex first second third firstBound secondBound thirdBound

def colorOne (color : WireColor) : Expr := existsE (2*var 1)
  (andE (colored 2 (var 0) (var 1) color)
    (.all (2*var 2) (impE (colored 3 (var 0) (var 2) color) (eqE (var 0) (var 1)))))

def colorAll (color : WireColor) : Expr := .all (2*var 1)
  (impE (ownerMatch 2 (var 0) (var 1)) (eqE (colorAt 2 (var 0)) (.literal (colorField color))))

def trichromatic : Expr := andE (colorOne .red) (andE (colorOne .green) (colorOne .blue))
def monochromatic : Expr := orE (colorAll .red) (orE (colorAll .green) (colorAll .blue))
def colorCheck : Expr := .ite (kind 1 (var 0)) trichromatic monochromatic
def guard : Expr := .all (var 5) (andE degree colorCheck)

theorem colorOne_truth (graph : Input) (vertex : Nat) (color : WireColor) :
    (colorOne color).Truth (vertex::input graph 0 0) ↔ (colors graph vertex).count color = 1 := by
  rw [color_one_iff]
  simp only [colorOne,truth_exists,truth_and,truth_all,truth_imp,truth_eq]
  change (∃ first < 2*graph.2.length, (colored 2 (var 0) (var 1) color).Truth
    (first::vertex::input graph 0 0) ∧ ∀ second < 2*graph.2.length,
      (colored 3 (var 0) (var 2) color).Truth (second::first::vertex::input graph 0 0) → second=first) ↔ _
  apply exists_congr; intro first
  apply and_congr_right; intro firstBound
  have firstAt := colored_truth graph [first,vertex] (var 0) (var 1) color firstBound
  change (colored 2 (var 0) (var 1) color).Truth (first::vertex::input graph 0 0) ↔
    (incidenceAt graph first).1 = vertex ∧ (incidenceAt graph first).2.2 = color at firstAt
  rw [firstAt]
  have allEqual : (∀ second < 2*graph.2.length,
      (colored 3 (var 0) (var 2) color).Truth (second::first::vertex::input graph 0 0) → second=first) ↔
      ∀ second < 2*graph.2.length, (incidenceAt graph second).1 = vertex →
        (incidenceAt graph second).2.2 = color → second=first := by
    apply forall_congr'; intro second
    apply forall_congr'; intro secondBound
    have secondAt := colored_truth graph [second,first,vertex] (var 0) (var 2) color secondBound
    change (colored 3 (var 0) (var 2) color).Truth (second::first::vertex::input graph 0 0) ↔
      (incidenceAt graph second).1 = vertex ∧ (incidenceAt graph second).2.2 = color at secondAt
    rw [secondAt]; exact and_imp
  rw [allEqual]
  tauto

theorem colorAll_truth (graph : Input) (vertex : Nat) (color : WireColor) :
    (colorAll color).Truth (vertex::input graph 0 0) ↔
      ∀ index < 2*graph.2.length, (incidenceAt graph index).1 = vertex → (incidenceAt graph index).2.2 = color := by
  simp only [colorAll,truth_all,truth_imp,truth_eq]
  change (∀ index < 2*graph.2.length, (ownerMatch 2 (var 0) (var 1)).Truth (index::vertex::input graph 0 0) →
    (colorAt 2 (var 0)).eval (index::vertex::input graph 0 0) = colorField color) ↔ _
  apply forall_congr'; intro index
  apply forall_congr'; intro bound
  have ownerAt := ownerMatch_truth graph [index,vertex] (var 0) (var 1) bound
  change (ownerMatch 2 (var 0) (var 1)).Truth (index::vertex::input graph 0 0) ↔
    (incidenceAt graph index).1 = vertex at ownerAt
  have colorAtIndex := colorAt_eval graph [index,vertex] (var 0) bound
  change (colorAt 2 (var 0)).eval (index::vertex::input graph 0 0) =
    colorField (incidenceAt graph index).2.2 at colorAtIndex
  rw [ownerAt,colorAtIndex,colorField_injective.eq_iff]

theorem trichromatic_truth (graph : Input) (vertex : Nat) :
    trichromatic.Truth (vertex::input graph 0 0) ↔ ∀ color : WireColor, (colors graph vertex).count color = 1 := by
  simp only [trichromatic,truth_and,colorOne_truth]
  constructor
  · intro h color; cases color <;> tauto
  · intro h; exact ⟨h .red,h .green,h .blue⟩

theorem monochromatic_truth (graph : Input) (vertex : Nat) :
    monochromatic.Truth (vertex::input graph 0 0) ↔ ∃ color : WireColor, ∀ c ∈ colors graph vertex, c = color := by
  rw [monochromatic_iff]
  simp only [monochromatic,truth_or,colorAll_truth]
  constructor
  · rintro (h | h | h)
    · exact ⟨.red,h⟩
    · exact ⟨.green,h⟩
    · exact ⟨.blue,h⟩
  · rintro ⟨color,h⟩; cases color <;> tauto

theorem guard_truth (graph : Input) : guard.Truth (input graph 0 0) ↔
    ∀ vertex < graph.1.length, (colors graph vertex).length = 3 ∧
      if graph.1.getD vertex false then ∀ color : WireColor, (colors graph vertex).count color = 1
      else ∃ color : WireColor, ∀ c ∈ colors graph vertex, c = color := by
  rw [guard,truth_all]
  change (∀ vertex < graph.1.length, (andE degree colorCheck).Truth (vertex::input graph 0 0)) ↔ _
  apply forall_congr'; intro vertex
  apply forall_congr'; intro bound
  rw [truth_and,degree_truth]
  apply and_congr_right; intro _
  have kindAt := kind_eval graph 0 0 [vertex] (var 0) bound
  change (kind 1 (var 0)).eval (vertex::input graph 0 0) = (graph.1.getD vertex false).toNat at kindAt
  cases isTri : graph.1.getD vertex false
  · simpa only [colorCheck,Truth,Expr.eval,kindAt,isTri,Bool.toNat_false,ite_true,Bool.false_eq_true,ite_false]
      using monochromatic_truth graph vertex
  · simpa only [colorCheck,Truth,Expr.eval,kindAt,isTri,Bool.toNat_true,Nat.one_ne_zero,ite_false,ite_true]
      using trichromatic_truth graph vertex

theorem guard_noPower : guard.noPower = true := by
  simp [guard,degree,witnesses,ownerMatch,colorCheck,kind,trichromatic,monochromatic,colorOne,colorAll,
    colored,colorAt,owner,entry,existsE,notE,eqE,orE,andE,impE,var,Expr.noPower]

end LeanTrominoes.TrichromaticGraphOrientation.VertexGuard
