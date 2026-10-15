/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Tromino.Finite.FiniteIPortalOwnership

/-! # Boolean network validity from one brick's local interface -/
noncomputable section
namespace LeanTrominoes.CompletionPattern.IBricks.FiniteGuards
open IBricks
set_option maxHeartbeats 2000000

structure BrickInterface (palette : Cell → Fin 24) (completed : Set (Finset Cell))
    (location : Cell) : Prop where
  states : ∀ entry∈layout (palette location), outsideAt completed location entry⊆entry.1.boundary ∧
    entry.1.pattern.Completable (outsideAt completed location entry)
  owners : ∀ entry∈layout (palette location), ∀ p∈entry.1.portCells, ∀ right : Bool,
    PortalOwners palette completed (Cell.add (atomMicroOffset location entry) p) right

theorem brickInterface_of_guards {palette : Cell → Fin 24} {completed : Set (Finset Cell)}
    (h : Tromino.I.IsFootprintTiling Set.univ completed) (location : Cell)
    (barriers : ∀ entry∈layout (palette location),BarrierRetained palette completed location entry)
    (own : ∀ entry∈layout (palette location),atomPrescribed location entry⊆completed)
    (owners : ∀ entry∈layout (palette location), ∀ p∈entry.1.portCells, ∀ right : Bool,
      PortalOwners palette completed (Cell.add (atomMicroOffset location entry) p) right) :
    BrickInterface palette completed location :=
  ⟨fun entry member => canonical_local_state palette location member h
    (barriers entry member) (own entry member),owners⟩

theorem canonical_port_proper {palette : Cell → Fin 24} {completed : Set (Finset Cell)}
    (h : Tromino.I.IsFootprintTiling Set.univ completed)
    (o : Occurrence palette) (interface : BrickInterface palette completed o.location) (p : Cell) (hp : p ∈ o.entry.1.portCells) :
    LocalProper (outsideAt completed o.location o.entry) p ↔
      ProperConnector palette completed (Cell.add (atomMicroOffset o.location o.entry) p) := by
  unfold LocalProper
  rw [canonical_port h o p hp false (interface.owners o.entry o.member p hp false),canonical_port h o p hp true (interface.owners o.entry o.member p hp true)]
  unfold ProperConnector
  split_ifs <;> tauto

theorem canonical_minor_forcing {palette : Cell → Fin 24} {completed : Set (Finset Cell)}
    (h : Tromino.I.IsFootprintTiling Set.univ completed)
    (o : Occurrence palette) (interface : BrickInterface palette completed o.location) :
    o.entry.1.PortForcing
      (ProperConnector palette completed (Cell.add (atomMicroOffset o.location o.entry) (0,0)))
      (ProperConnector palette completed (Cell.add (atomMicroOffset o.location o.entry) (0,1))) := by
  have localState := interface.states o.entry o.member
  cases atomEq : o.entry.1
  case copy => trivial
  case clause => trivial
  all_goals
    have top : (0,0) ∈ o.entry.1.portCells := by rw [atomEq]; decide
    have bottom : (0,1) ∈ o.entry.1.portCells := by rw [atomEq]; decide
    rw [← canonical_port_proper h o interface _ top,← canonical_port_proper h o interface _ bottom]
    rw [atomEq] at localState
  · exact equal_propagates_proper _ localState.1 localState.2
  · exact Atom.forces_proper .negate (Or.inl rfl) _ localState.1 localState.2
  · exact Atom.forces_proper .plugTop (Or.inr (Or.inl rfl)) _ localState.1 localState.2
  · exact Atom.forces_proper .plugBottom (Or.inr (Or.inr rfl)) _ localState.1 localState.2

/-- Every connector used by a subbrick of a completed plane is Boolean. -/
theorem all_canonical_ports_proper {palette : Cell → Fin 24} {completed : Set (Finset Cell)}
    (h : Tromino.I.IsFootprintTiling Set.univ completed)
    (location : Cell) (interface : BrickInterface palette completed location) : ∀ entry ∈ layout (palette location), ∀ p ∈ entry.1.portCells,
      ProperConnector palette completed (Cell.add (atomMicroOffset location entry) p) := by
  let proper : Cell → Prop := fun p => ProperConnector palette completed (Cell.add (brickMicroOrigin location) p)
  have associate (entry : Atom × Cell) (p : Cell) :
      Cell.add (atomMicroOffset location entry) p =
        Cell.add (brickMicroOrigin location) (Cell.add (entryMicroOffset entry) p) := by
    apply Prod.ext <;> dsimp [atomMicroOffset,Cell.add] <;> omega
  have forcing : ForcingNetwork (palette location) proper := by
    intro entry he
    have supplied := canonical_minor_forcing h (Occurrence.mk location entry he) interface
    dsimp only at supplied
    rw [associate entry (0,0),associate entry (0,1)] at supplied
    exact supplied
  intro entry he p hp
  rw [associate]
  exact forcing_all_ports (palette location) proper forcing entry he p hp

/-- Every canonical local state equals the state selected by one global
Boolean connector assignment. Outer not/plug rows exclude non-Boolean states. -/
theorem canonical_outside_boolean {palette : Cell → Fin 24} {completed : Set (Finset Cell)}
    (h : Tromino.I.IsFootprintTiling Set.univ completed)
    (o : Occurrence palette) (interface : BrickInterface palette completed o.location) :
    outsideAt completed o.location o.entry = o.entry.1.booleanOutside
      (fun p => canonicalValue palette completed (Cell.add (atomMicroOffset o.location o.entry) p)) := by
  have localState := interface.states o.entry o.member
  ext c
  by_cases boundary : c ∈ o.entry.1.boundary
  · obtain ⟨p,hp,right,rfl⟩ := o.entry.1.boundary_ports c boundary
    rw [canonical_port h o p hp right (interface.owners o.entry o.member p hp right),o.entry.1.port_boolean_outside _ p hp right]
    have proper := all_canonical_ports_proper h o.location interface o.entry o.member p hp
    rw [outside_below_value proper right]
  · have absent : c ∉ outsideAt completed o.location o.entry := fun hc => boundary (localState.1 hc)
    rw [o.entry.1.boolean_outside_on_boundary]
    simp [Finset.mem_filter,boundary,absent]

/-- The extracted connector values satisfy every subbrick's Boolean relation. -/
theorem canonical_global_relations {palette : Cell → Fin 24} {completed : Set (Finset Cell)}
    (h : Tromino.I.IsFootprintTiling Set.univ completed)
    (o : Occurrence palette) (interface : BrickInterface palette completed o.location) :
    o.entry.1.BooleanRelation
      (fun p => canonicalValue palette completed (Cell.add (atomMicroOffset o.location o.entry) p)) := by
  rw [← Atom.boolean_completion_iff,← canonical_outside_boolean h o interface]
  exact (interface.states o.entry o.member).2

theorem canonical_table_valid {palette : Cell → Fin 24} {completed : Set (Finset Cell)}
    (h : Tromino.I.IsFootprintTiling Set.univ completed)
    (location : Cell) (interface : BrickInterface palette completed location) :
    BrickBooleanRelation (palette location) (tableOfValue (canonicalValue palette completed) location) := by
  intro entry he
  let o : Occurrence palette := ⟨location,entry,he⟩
  apply (entry.1.boolean_relation_congr _
    (fun c => canonicalValue palette completed (Cell.add (atomMicroOffset location entry) c)) ?_).mpr
  · exact canonical_global_relations h o interface
  · intro c hc
    have bound := brick_port_window (palette location) entry he c hc
    simp only [Finset.mem_product,Finset.mem_Ico] at bound
    rw [table_of_value_window _ _ _ ⟨bound.1.1,bound.1.2,bound.2.1,bound.2.2⟩]
    congr 1
    apply Prod.ext <;> dsimp [atomMicroOffset,Cell.add] <;> omega

/-- Validity at a guarded brick uses no distant preplacement assumption. -/
theorem canonical_network_valid {palette : Cell → Fin 24} {completed : Set (Finset Cell)}
    (h : Tromino.I.IsFootprintTiling Set.univ completed) (location : Cell)
    (interface : BrickInterface palette completed location) :
    Network (palette location)
      (tableExternal (tableOfValue (canonicalValue palette completed) location)) :=
  network_of_brick_table _ _ (canonical_table_valid h location interface)
end LeanTrominoes.CompletionPattern.IBricks.FiniteGuards
