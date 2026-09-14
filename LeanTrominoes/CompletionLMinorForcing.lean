/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionLCanonicalConnectors

noncomputable section
namespace LeanTrominoes.CompletionPattern.LBricks

set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

def LocalProper (outside : Finset Cell) (p : Cell) : Prop :=
  portalCell p false ∈ outside ↔ portalCell p true ∉ outside

instance (outside : Finset Cell) (p : Cell) : Decidable (LocalProper outside p) := by
  unfold LocalProper
  infer_instance

theorem minor_outside_proper (top bottom : Bool) :
    LocalProper (minorOutside top bottom) (0,0) ∧ LocalProper (minorOutside top bottom) (0,1) := by
  revert top bottom
  decide +kernel

theorem equal_propagates_proper (outside : Finset Cell) (subset : outside ⊆ minorBoundary)
    (h : LEqBoundary.pattern.Completable outside) :
    LocalProper outside (0,0) ↔ LocalProper outside (0,1) := by
  obtain ⟨i,rfl⟩ := minor_boundary_exhaustive outside (Finset.mem_powerset.mpr subset)
  rw [l_eq_boundary] at h
  have checked : ∀ j : Fin 16, (j = 3 ∨ j = 6 ∨ j = 9 ∨ j = 12) →
      (LocalProper (LEqBoundary.outside j) (0,0) ↔ LocalProper (LEqBoundary.outside j) (0,1)) := by decide +kernel
  exact checked i h

theorem Atom.forces_proper (a : Atom) (forcing : a = .negate ∨ a = .plugTop ∨ a = .plugBottom)
    (outside : Finset Cell) (subset : outside ⊆ a.boundary) (h : a.pattern.Completable outside) :
    LocalProper outside (0,0) ∧ LocalProper outside (0,1) := by
  rcases forcing with rfl | rfl | rfl
  · obtain ⟨v,rfl⟩ := (neg_states outside subset).mp h
    exact minor_outside_proper v (!v)
  · obtain ⟨v,rfl⟩ := (plug_top_states outside subset).mp h
    exact minor_outside_proper false v
  · obtain ⟨v,rfl⟩ := (plug_bottom_states outside subset).mp h
    exact minor_outside_proper v false

theorem canonical_port_proper {palette : Cell → Fin 24} {completed : Set (Finset Cell)}
    (h : Tromino.L.IsFootprintTiling Set.univ completed) (retained : globalPrescribed palette ⊆ completed)
    (o : Occurrence palette) (p : Cell) (hp : p ∈ o.entry.1.portCells) :
    LocalProper (outsideAt completed o.location o.entry) p ↔
      ProperConnector palette completed (Cell.add (atomMicroOffset o.location o.entry) p) := by
  unfold LocalProper
  rw [canonical_port h retained o p hp false,canonical_port h retained o p hp true]
  unfold ProperConnector
  split_ifs <;> tauto

def Atom.PortForcing (a : Atom) (top bottom : Prop) : Prop :=
  match a with
  | .equal => top ↔ bottom
  | .negate | .plugTop | .plugBottom => top ∧ bottom
  | _ => True

/-- Each minor subbrick either forces both global connectors to be Boolean
or propagates Booleanity from either end to the other. -/
theorem canonical_minor_forcing {palette : Cell → Fin 24} {completed : Set (Finset Cell)}
    (h : Tromino.L.IsFootprintTiling Set.univ completed) (retained : globalPrescribed palette ⊆ completed)
    (o : Occurrence palette) :
    o.entry.1.PortForcing
      (ProperConnector palette completed (Cell.add (atomMicroOffset o.location o.entry) (0,0)))
      (ProperConnector palette completed (Cell.add (atomMicroOffset o.location o.entry) (0,1))) := by
  have localState := canonical_local_state palette o.location o.member h retained
  cases atomEq : o.entry.1
  case copy => trivial
  case clause => trivial
  all_goals
    have top : (0,0) ∈ o.entry.1.portCells := by rw [atomEq]; decide
    have bottom : (0,1) ∈ o.entry.1.portCells := by rw [atomEq]; decide
    rw [← canonical_port_proper h retained o _ top,← canonical_port_proper h retained o _ bottom]
    rw [atomEq] at localState
  · exact equal_propagates_proper _ localState.1 localState.2
  · exact Atom.forces_proper .negate (Or.inl rfl) _ localState.1 localState.2
  · exact Atom.forces_proper .plugTop (Or.inr (Or.inl rfl)) _ localState.1 localState.2
  · exact Atom.forces_proper .plugBottom (Or.inr (Or.inr rfl)) _ localState.1 localState.2

end LeanTrominoes.CompletionPattern.LBricks
