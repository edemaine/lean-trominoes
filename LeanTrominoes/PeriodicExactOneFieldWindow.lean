/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFFieldWindow
import LeanTrominoes.PeriodicExactOneCNFLocality

/-! # Field-indexed windows for local one-dimensional exact-one SAT -/
namespace LeanTrominoes.PeriodicCNF.ExactOneFieldWindow
open FieldWindow PeriodicOneInThree

def Valid (f : PeriodicCNF Nat) (w : Window f) : Prop :=
  ∀ c ∈ f.clauses, ExactlyOne (c.map fun l =>
    value f l.atom (w (LineWindow.position c l)) == l.value)

theorem satisfiable_iff (f : PeriodicCNF Nat) (horizontal : f.IsOneDimensional)
    (locality : f.IsLocalOnLine) :
    PeriodicOneInThree.Satisfiable f ↔ LocalWindow.Satisfiable 2 (Valid f) := by
  constructor
  · rintro ⟨assignment,satisfies⟩
    refine ⟨fun x p => assignment ((PeriodicCNFFlatEncoding.formulaFields f)[p.val]?.getD 0) (x,0),?_⟩
    intro x c hc
    have holds := satisfies (x+1-LineWindow.anchor c,0) c hc
    change ExactlyOne (c.map _) at holds ⊢
    convert holds using 1
    apply List.map_congr_left
    intro l hl
    have pos := LineWindow.position_eq (locality c hc) hl
    have vert := horizontal c hc l hl
    change (value f l.atom (fun p => assignment
      ((PeriodicCNFFlatEncoding.formulaFields f)[p.val]?.getD 0)
      (x+(LineWindow.position c l).val,0)) == l.value) = _
    rw [value_of_assignment f hc hl (fun a => assignment a (x+(LineWindow.position c l).val,0))]
    congr 2
    simp only [Cell.add,vert,add_zero]
    congr 1
    omega
  · rintro ⟨configuration,valid⟩
    refine ⟨fun a p => value f a (configuration p.1),?_⟩
    intro x c hc
    have holds := valid (x.1+LineWindow.anchor c-1) c hc
    change ExactlyOne (c.map _) at holds ⊢
    convert holds using 1
    apply List.map_congr_left
    intro l hl
    have pos := LineWindow.position_eq (locality c hc) hl
    change (value f l.atom (configuration (x.1+l.offset.1)) == l.value) =
      (value f l.atom (configuration ((x.1+LineWindow.anchor c-1)+(LineWindow.position c l).val)) == l.value)
    have eq : x.1+l.offset.1 = (x.1+LineWindow.anchor c-1)+(LineWindow.position c l).val := by omega
    rw [eq]

def packedTransition (f : PeriodicCNF Nat) (first second : Nat) : Prop :=
  LocalWindow.Transition (Valid f) (decodeWord f first) (decodeWord f second)

theorem satisfiable_iff_packed_cycle (f : PeriodicCNF Nat)
    (horizontal : f.IsOneDimensional) (locality : f.IsLocalOnLine) :
    PeriodicOneInThree.Satisfiable f ↔ FiniteState.HasCycle
      (fun a b : PackedState f => packedTransition f a.val b.val) := by
  rw [satisfiable_iff f horizontal locality,LocalWindow.satisfiable_iff_cycle]
  constructor
  · rintro ⟨period,states,step⟩
    refine ⟨period,fun i => ⟨encodeWindow f (states i),encodeWindow_lt f (states i)⟩,?_⟩
    intro i
    simpa only [packedTransition,decodeWord_encodeWindow] using step i
  · rintro ⟨period,states,step⟩
    exact ⟨period,fun i => decodeWord f (states i).val,step⟩
end LeanTrominoes.PeriodicCNF.ExactOneFieldWindow
