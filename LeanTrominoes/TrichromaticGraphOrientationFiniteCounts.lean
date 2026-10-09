/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrichromaticGraphOrientationFinite
import LeanTrominoes.BoolCoherentCount

/-! # Finite orientation constraints as inward counts -/
namespace LeanTrominoes.TrichromaticGraphOrientation
open Gadget PeriodicOneInThree

theorem coherent_values_iff (assignment : Nat → Cell → Bool) (cell : Cell) (literals : PeriodicClause Nat) :
    Coherent assignment cell literals ↔
      ∀ first ∈ clauseValues assignment cell literals, ∀ second ∈ clauseValues assignment cell literals, first=second := by
  have holds (literal : PeriodicLiteral Nat) :
      (assignment literal.atom (Cell.add cell literal.offset) == literal.value)=true ↔ literal.Holds assignment cell := by
    simp [PeriodicLiteral.Holds]
  have boolEq (first second : Bool) : (first=true ↔ second=true) ↔ first=second := by
    cases first <;> cases second <;> decide
  constructor
  · intro coherent first firstMember second secondMember
    obtain ⟨l,lMember,rfl⟩ := List.mem_map.mp firstMember
    obtain ⟨r,rMember,rfl⟩ := List.mem_map.mp secondMember
    apply (boolEq _ _).mp
    rw [holds,holds]
    exact coherent l lMember r rMember
  · intro coherent first firstMember second secondMember
    rw [← holds first,← holds second]
    apply (boolEq _ _).mpr
    exact coherent _ (List.mem_map.mpr ⟨first,firstMember,rfl⟩)
      _ (List.mem_map.mpr ⟨second,secondMember,rfl⟩)

theorem coherent_count_iff (assignment : Nat → Cell → Bool) (cell : Cell) (literals : PeriodicClause Nat) :
    Coherent assignment cell literals ↔
      (clauseValues assignment cell literals).count true=0 ∨
        (clauseValues assignment cell literals).count true=literals.length := by
  rw [coherent_values_iff,bool_coherent_iff_count]
  simp only [clauseValues,List.length_map]

def finiteInwardCount (graph : Input) (assignment : Nat → Bool) (vertex : Nat) : Nat :=
  (clauseValues (fun edge _ => assignment edge) (0,0) (incoming graph vertex)).count true

def FiniteCountConstraints (graph : Input) (assignment : Nat → Bool) : Prop :=
  ∀ vertex < graph.1.length,
    if graph.1.getD vertex false then finiteInwardCount graph assignment vertex=0 ∨ finiteInwardCount graph assignment vertex=3
    else finiteInwardCount graph assignment vertex=1

theorem finiteIsOrientation_iff_counts (graph : Input) (wellFormed : IsWellFormed graph) (assignment : Nat → Bool) :
    FiniteIsOrientation graph assignment ↔ FiniteCountConstraints graph assignment := by
  have degree (vertex : Nat) (bound : vertex < graph.1.length) : (incoming graph vertex).length=3 := by
    simpa only [incoming,colors,List.length_map] using (wellFormed.2 vertex bound).1
  constructor
  · intro oriented vertex bound
    have original := oriented (0,0) vertex bound
    cases kind : graph.1.getD vertex false with
    | true =>
      simp only [kind,if_true] at original ⊢
      simpa only [finiteInwardCount,degree vertex bound] using (coherent_count_iff _ _ _).mp original
    | false =>
      simp only [kind,Bool.false_eq_true,if_false] at original ⊢
      exact original
  · intro counted cell vertex bound
    have original := counted vertex bound
    cases kind : graph.1.getD vertex false with
    | true =>
      simp only [kind,if_true] at original ⊢
      apply (coherent_count_iff _ _ _).mpr
      simpa only [finiteInwardCount,degree vertex bound,clauseValues] using original
    | false =>
      simp only [kind,Bool.false_eq_true,if_false] at original ⊢
      exact original

end LeanTrominoes.TrichromaticGraphOrientation
