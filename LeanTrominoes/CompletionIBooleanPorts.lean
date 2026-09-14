/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionIBooleanStates
import LeanTrominoes.CompletionIMinorStates
import LeanTrominoes.CompletionIGuardedRelations

noncomputable section
namespace LeanTrominoes.CompletionPattern.IBricks

set_option maxHeartbeats 0
set_option maxRecDepth 16384

theorem Atom.boundary_inside (a : Atom) : a.boundary ⊆ a.pattern.region := by
  cases a <;> decide +kernel

theorem Atom.boolean_outside_on_boundary (a : Atom) (value : Cell → Bool) :
    a.booleanOutside value = a.boundary.filter (fun c => booleanMicroOwner value c ∉ a.group) := by
  ext c
  simp only [Atom.booleanOutside,Finset.mem_filter]
  constructor
  · rintro ⟨inside,notOwned⟩
    refine ⟨?_,notOwned⟩
    by_contra notBoundary
    rw [a.region_group] at inside
    rw [a.boundary_group] at notBoundary
    exact notOwned (micro_in_group (Finset.mem_sdiff.mpr ⟨inside,notBoundary⟩) (boolean_owner_contains value c))
  · rintro ⟨boundary,notOwned⟩
    exact ⟨a.boundary_inside boundary,notOwned⟩

def connectorOutside (a : Atom) (value : Cell → Bool) : Finset Cell :=
  match a with
  | .copy =>
      {(if value (0,0) then 14 else 5,0),(if value (1,0) then 32 else 23,0),
       (if value (0,2) then 5 else 14,54),(if value (1,2) then 23 else 32,54)}
  | .clause =>
      {(if value (0,0) then 14 else 5,0),(if value (1,0) then 32 else 23,0),
       (if value (0,1) then 5 else 14,27),(if value (1,1) then 23 else 32,27)}
  | _ => minorOutside (value (0,0)) (value (0,1))

/-- Pixel ownership gives exactly the proper Boolean boundary states used
by the independently checked ASCII-gadget certificates. -/
theorem boolean_outside_connectors (a : Atom) (value : Cell → Bool) :
    a.booleanOutside value = connectorOutside a value := by
  rw [a.boolean_outside_on_boundary]
  cases a <;>
    cases h00 : value (0,0) <;> cases h10 : value (1,0) <;>
    cases h01 : value (0,1) <;> cases h11 : value (1,1) <;>
    cases h02 : value (0,2) <;> cases h12 : value (1,2) <;>
    simp [Finset.filter_insert,Finset.filter_singleton,Atom.boundary,Atom.group,connectorOutside,minorOutside,
      booleanMicroOwner,aboveMicro,h00,h10,h01,h11,h02,h12]

theorem minor_outside_table (top bottom : Bool) :
    minorOutside top bottom = IGuardedEqBoundary.outside (state4 (!top) top bottom (!bottom)) := by
  revert top bottom
  decide +kernel

theorem equal_boolean_ports (value : Cell → Bool) :
    Atom.equal.pattern.Completable (Atom.equal.booleanOutside value) ↔ value (0,0) = value (0,1) := by
  rw [boolean_outside_connectors]
  change IGuardedEqBoundary.pattern.Completable (minorOutside _ _) ↔ _
  rw [minor_outside_table,i_guarded_eq_boundary]
  cases value (0,0) <;> cases value (0,1) <;> decide +kernel

theorem negate_boolean_ports (value : Cell → Bool) :
    Atom.negate.pattern.Completable (Atom.negate.booleanOutside value) ↔ value (0,0) ≠ value (0,1) := by
  rw [boolean_outside_connectors]
  change IGuardedNegBoundary.pattern.Completable (minorOutside _ _) ↔ _
  rw [minor_outside_table,(minor_boundary_data _).1,i_guarded_neg_boundary]
  cases value (0,0) <;> cases value (0,1) <;> decide +kernel

theorem plug_top_boolean_ports (value : Cell → Bool) :
    Atom.plugTop.pattern.Completable (Atom.plugTop.booleanOutside value) ↔ value (0,0) = false := by
  rw [boolean_outside_connectors]
  change IGuardedPlugTopBoundary.pattern.Completable (minorOutside _ _) ↔ _
  rw [minor_outside_table,(minor_boundary_data _).2.1,i_guarded_plugtop_boundary]
  cases value (0,0) <;> cases value (0,1) <;> decide +kernel

theorem plug_bottom_boolean_ports (value : Cell → Bool) :
    Atom.plugBottom.pattern.Completable (Atom.plugBottom.booleanOutside value) ↔ value (0,1) = false := by
  rw [boolean_outside_connectors]
  change IGuardedPlugBotBoundary.pattern.Completable (minorOutside _ _) ↔ _
  rw [minor_outside_table,(minor_boundary_data _).2.2,i_guarded_plugbot_boundary]
  cases value (0,0) <;> cases value (0,1) <;> decide +kernel

theorem copy_outside_table (value : Cell → Bool) :
    connectorOutside .copy value = IGuardedDup.outside (state4 (value (0,0)) (value (1,0)) (value (0,2)) (value (1,2))) := by
  simp only [connectorOutside]
  cases value (0,0) <;> cases value (1,0) <;> cases value (0,2) <;> cases value (1,2) <;> decide +kernel

theorem clause_outside_table (value : Cell → Bool) :
    connectorOutside .clause value = IGuardedTftsat.outside (state4 (value (0,0)) (value (1,0)) (value (0,1)) (value (1,1))) := by
  simp only [connectorOutside]
  cases value (0,0) <;> cases value (1,0) <;> cases value (0,1) <;> cases value (1,1) <;> decide +kernel

theorem copy_boolean_ports (value : Cell → Bool) :
    Atom.copy.pattern.Completable (Atom.copy.booleanOutside value) ↔
      value (0,0) = value (1,0) ∧ value (1,0) = value (0,2) ∧ value (0,2) = value (1,2) := by
  rw [boolean_outside_connectors,copy_outside_table]
  exact i_guarded_duplicator _ _ _ _

theorem clause_boolean_ports (value : Cell → Bool) :
    Atom.clause.pattern.Completable (Atom.clause.booleanOutside value) ↔
      value (1,1) = false ∧ (value (0,0) = true ∨ value (1,0) = false ∨ value (0,1) = true) := by
  rw [boolean_outside_connectors,clause_outside_table]
  exact i_guarded_clause _ _ _ _

end LeanTrominoes.CompletionPattern.IBricks
