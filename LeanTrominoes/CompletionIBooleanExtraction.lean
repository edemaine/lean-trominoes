/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionIBrickForcing

noncomputable section
namespace LeanTrominoes.CompletionPattern.IBricks

set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

theorem Atom.boundary_ports (a : Atom) : ∀ c ∈ a.boundary,
    ∃ p ∈ a.portCells, ∃ right : Bool, c = portalCell p right := by
  cases a <;> decide +kernel

theorem Atom.port_pixel_boundary (a : Atom) : ∀ p ∈ a.portCells, ∀ right : Bool,
    portalCell p right ∈ a.boundary := by
  cases a <;> decide +kernel

theorem Atom.port_boolean_outside (a : Atom) (value : Cell → Bool) (p : Cell)
    (hp : p ∈ a.portCells) (right : Bool) :
    portalCell p right ∈ a.booleanOutside value ↔
      if p.2 = 0 then value p = right else value p ≠ right := by
  rw [a.boolean_outside_on_boundary,Finset.mem_filter]
  have boundary := a.port_pixel_boundary p hp right
  have ownership := a.port_ownership p hp
  rw [boolean_owner_portal]
  by_cases top : p.2 = 0
  · rw [if_pos top] at ownership ⊢
    by_cases same : value p = right <;> simp [same,boundary,ownership.1,ownership.2]
  · rw [if_neg top] at ownership ⊢
    by_cases same : value p = right <;> simp [same,boundary,ownership.1,ownership.2]

theorem outside_below_value {palette : Cell → Fin 24} {completed : Set (Finset Cell)}
    {i : Cell} (proper : ProperConnector palette completed i) (right : Bool) :
    OutsideBelow palette completed i right ↔ canonicalValue palette completed i = right := by
  classical
  unfold ProperConnector at proper
  cases right
  · rw [proper]
    simp [canonicalValue]
  · simp [canonicalValue]

/-- Every canonical local state equals the state selected by one global
Boolean connector assignment. Outer not/plug rows exclude non-Boolean states. -/
theorem canonical_outside_boolean {palette : Cell → Fin 24} {completed : Set (Finset Cell)}
    (h : Tromino.I.IsFootprintTiling Set.univ completed) (retained : globalPrescribed palette ⊆ completed)
    (o : Occurrence palette) :
    outsideAt completed o.location o.entry = o.entry.1.booleanOutside
      (fun p => canonicalValue palette completed (Cell.add (atomMicroOffset o.location o.entry) p)) := by
  have localState := canonical_local_state palette o.location o.member h retained
  ext c
  by_cases boundary : c ∈ o.entry.1.boundary
  · obtain ⟨p,hp,right,rfl⟩ := o.entry.1.boundary_ports c boundary
    rw [canonical_port h retained o p hp right,o.entry.1.port_boolean_outside _ p hp right]
    have proper := all_canonical_ports_proper h retained o.location o.entry o.member p hp
    rw [outside_below_value proper right]
  · have absent : c ∉ outsideAt completed o.location o.entry := fun hc => boundary (localState.1 hc)
    rw [o.entry.1.boolean_outside_on_boundary]
    simp [Finset.mem_filter,boundary,absent]

/-- The extracted connector values satisfy every subbrick's Boolean relation. -/
theorem canonical_global_relations {palette : Cell → Fin 24} {completed : Set (Finset Cell)}
    (h : Tromino.I.IsFootprintTiling Set.univ completed) (retained : globalPrescribed palette ⊆ completed)
    (o : Occurrence palette) :
    o.entry.1.BooleanRelation
      (fun p => canonicalValue palette completed (Cell.add (atomMicroOffset o.location o.entry) p)) := by
  rw [← Atom.boolean_completion_iff,← canonical_outside_boolean h retained o]
  exact (canonical_local_state palette o.location o.member h retained).2

end LeanTrominoes.CompletionPattern.IBricks
