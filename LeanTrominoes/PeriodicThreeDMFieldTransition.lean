/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeDMFieldPredicate

/-! # Arithmetic matching transitions agree with the finite overlap graph -/
namespace LeanTrominoes.PeriodicThreeDM.FieldPredicate
open Gadget FlatEncoding FieldQueries BoundedArithmetic BoundedArithmetic.Expr

theorem colorValid_typed (p : PeriodicThreeDM) (a b : Nat) (color : WireColor) :
    (colorValid color).Truth (input p a b) ↔ ∀ v < p.elementCount color,
      PeriodicOneInThree.ExactlyOne ((p.incidences color v).map fun i =>
        LineWindow.value p i.tripleIndex (LineWindow.decodeWord p a (LineWindow.position i))) := by
  rw [colorValid,truth_all]
  have count := count_eval p [p.triples.length,0,0,a,b] color
  change (var (5+colorIndex color)).eval (input p a b) = p.elementCount color at count
  rw [count]
  apply forall_congr'
  intro v
  apply forall_congr'
  intro hv
  rw [LineWindow.exactlyOne_iff_unique]
  simp only [truth_exists,truth_and,truth_all,truth_imp,truth_eq]
  change (∃ j < p.triples.length, (selected 2 color (var 0) (var 1)).Truth (j::v::input p a b) ∧
    ∀ k < p.triples.length, (selected 3 color (var 0) (var 2)).Truth (k::j::v::input p a b) → k=j) ↔ _
  apply exists_congr
  intro j
  apply and_congr_right
  intro hj
  have sj := selected_truth p a b [j,v] color (var 0) (var 1) hj
  change (selected 2 color (var 0) (var 1)).Truth (j::v::input p a b) ↔ LineWindow.Selected p color v a j at sj
  rw [sj]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro k
  apply forall_congr'
  intro hk
  have sk := selected_truth p a b [k,j,v] color (var 0) (var 2) hk
  change (selected 3 color (var 0) (var 2)).Truth (k::j::v::input p a b) ↔ LineWindow.Selected p color v a k at sk
  rw [sk]

theorem valid_typed (p : PeriodicThreeDM) (a b : Nat) :
    valid.Truth (input p a b) ↔ LineWindow.Valid p (LineWindow.decodeWord p a) := by
  simp only [valid,truth_and,colorValid_typed,LineWindow.Valid]
  constructor
  · intro h color; cases color <;> tauto
  · intro h; exact ⟨h .red,h .green,h .blue⟩

theorem overlap_typed (p : PeriodicThreeDM) (a b : Nat) :
    overlap.Truth (input p a b) ↔ ∀ i : Fin 2,
      LineWindow.decodeWord p a i.succ = LineWindow.decodeWord p b i.castSucc := by
  change PeriodicCNF.FieldPredicate.overlap.Truth
    (PeriodicCNF.FieldPredicate.context p.triples.length 0 0 a b (fields p)) ↔ _
  rw [PeriodicCNF.FieldPredicate.overlap_correct]
  constructor
  · intro raw i
    funext j
    fin_cases i
    · change a.testBit (j.val+p.triples.length*1) = b.testBit (j.val+p.triples.length*0)
      simpa using (raw j.val j.isLt).1
    · change a.testBit (j.val+p.triples.length*2) = b.testBit (j.val+p.triples.length*1)
      simpa using (raw j.val j.isLt).2
  · intro typed j hj
    have h0 := congrFun (typed 0) ⟨j,hj⟩
    have h1 := congrFun (typed 1) ⟨j,hj⟩
    change a.testBit (j+p.triples.length*1) = b.testBit (j+p.triples.length*0) at h0
    change a.testBit (j+p.triples.length*2) = b.testBit (j+p.triples.length*1) at h1
    simpa [PeriodicCNF.FieldPredicate.Overlap] using And.intro h0 h1

theorem transition_typed (p : PeriodicThreeDM) (a b : Nat) :
    transition.Truth (input p a b) ↔ LineWindow.packedTransition p a b := by
  rw [transition,truth_and,valid_typed,overlap_typed]
  rfl

theorem check_true (p : PeriodicThreeDM) (a b : Nat) :
    check p a b = true ↔ LineWindow.packedTransition p a b := by
  simpa only [check,decide_eq_true_eq,Truth] using transition_typed p a b

theorem cycle_iff (p : PeriodicThreeDM) (horizontal : p.IsOneDimensional) (locality : p.IsLocal) :
    FiniteState.HasCycle (fun a b : LineWindow.PackedState p => check p a.val b.val=true) ↔ p.Satisfiable := by
  rw [LineWindow.satisfiable_iff_packed_cycle p horizontal locality]
  constructor
  · rintro ⟨period,states,steps⟩
    exact ⟨period,states,fun i => (check_true p _ _).mp (steps i)⟩
  · rintro ⟨period,states,steps⟩
    exact ⟨period,states,fun i => (check_true p _ _).mpr (steps i)⟩

end LeanTrominoes.PeriodicThreeDM.FieldPredicate
