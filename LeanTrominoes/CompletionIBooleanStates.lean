/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionIBooleanOwnership

noncomputable section
namespace LeanTrominoes.CompletionPattern.IBricks

set_option maxHeartbeats 2000000

/-- The outside cells selected by a global Boolean connector assignment. -/
def booleanOutside {palette : Cell → Fin 24} (value : Cell → Bool) (o : Occurrence palette) : Finset Cell :=
  o.entry.1.pattern.region.filter fun c =>
    booleanMicroOwner value (Cell.add (atomOffset o.location o.entry) c) ∉ groupAt o.location o.entry

theorem boolean_outside_boundary {palette : Cell → Fin 24} (value : Cell → Bool)
    (o : Occurrence palette) : booleanOutside value o ⊆ o.entry.1.boundary := by
  intro c hc
  obtain ⟨inside,notOwned⟩ := Finset.mem_filter.mp hc
  by_contra notBoundary
  exact notOwned (core_micro_owner palette o.location o.member
    (Finset.mem_sdiff.mpr ⟨inside,notBoundary⟩) (boolean_owner_contains value _))

theorem boolean_state_target {palette : Cell → Fin 24} (value : Cell → Bool) (o : Occurrence palette) :
    stateTarget o (booleanOutside value o) = booleanGroupRegion value (groupAt o.location o.entry) := by
  classical
  ext c
  constructor
  · intro hc
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨inside,notOutside⟩ := Finset.mem_sdiff.mp hd
    apply Finset.mem_filter.mpr
    constructor
    · rw [group_at_region palette o.location o.member]
      exact Finset.mem_image.mpr ⟨d,inside,rfl⟩
    · by_contra notOwned
      exact notOutside (Finset.mem_filter.mpr ⟨inside,notOwned⟩)
  · intro hc
    obtain ⟨inside,owned⟩ := Finset.mem_filter.mp hc
    rw [group_at_region palette o.location o.member] at inside
    obtain ⟨d,hd,eq⟩ := Finset.mem_image.mp inside
    refine Finset.mem_image.mpr ⟨d,Finset.mem_sdiff.mpr ⟨hd,?_⟩,eq⟩
    intro outside
    have notOwned := (Finset.mem_filter.mp outside).2
    change booleanMicroOwner value (Cell.add (Cell.add (origin o.location) o.entry.2) d) ∉ _ at notOwned
    rw [eq] at notOwned
    exact notOwned owned

/-- Realizing the Boolean state at every individual subbrick suffices to
complete the entire plane. Pixel ownership supplies all geometric gluing. -/
theorem completion_of_boolean_states (palette : Cell → Fin 24) (value : Cell → Bool)
    (realized : ∀ o : Occurrence palette, o.entry.1.pattern.Completable (booleanOutside value o)) :
    Tromino.I.Completable Set.univ (globalPrescribed palette) := by
  apply completion_of_compatible_states palette (outside := booleanOutside value)
  constructor
  · intro o
    exact ⟨boolean_outside_boundary value o,realized o⟩
  · intro c
    have partition := boolean_groups_partition palette value c
    simpa only [boolean_state_target] using partition

/-- Microcell ownership commutes with translating the Boolean assignment. -/
theorem boolean_owner_translation (value : Cell → Bool) (delta c : Cell) :
    booleanMicroOwner value (Cell.add (microOrigin delta) c) =
      Cell.add delta (booleanMicroOwner (fun i => value (Cell.add delta i)) c) := by
  have base : ((Cell.add (microOrigin delta) c).1 / 18,(Cell.add (microOrigin delta) c).2 / 27) =
      Cell.add delta (c.1 / 18,c.2 / 27) := by
    apply Prod.ext <;> dsimp [Cell.add,microOrigin] <;> omega
  have x : (Cell.add (microOrigin delta) c).1 % 18 = c.1 % 18 := by
    dsimp [Cell.add,microOrigin]; omega
  have y : (Cell.add (microOrigin delta) c).2 % 27 = c.2 % 27 := by
    dsimp [Cell.add,microOrigin]; omega
  unfold booleanMicroOwner
  rw [base,x,y]
  dsimp only
  split_ifs <;> apply Prod.ext <;> dsimp [aboveMicro,Cell.add] <;> omega

def Atom.booleanOutside (a : Atom) (value : Cell → Bool) : Finset Cell :=
  a.pattern.region.filter fun c => booleanMicroOwner value c ∉ a.group

theorem boolean_outside_local {palette : Cell → Fin 24} (value : Cell → Bool) (o : Occurrence palette) :
    booleanOutside value o = o.entry.1.booleanOutside
      (fun i => value (Cell.add (atomMicroOffset o.location o.entry) i)) := by
  ext c
  simp only [booleanOutside,Atom.booleanOutside,Finset.mem_filter]
  rw [← atom_micro_offset palette o.location o.member,boolean_owner_translation,group_at_image]
  simp only [Finset.mem_image,(Cell.add_left_injective (atomMicroOffset o.location o.entry)).eq_iff]
  simp

end LeanTrominoes.CompletionPattern.IBricks
