/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionIBoundaryNeighbors

/-! # Assigning shared connector pixels from Boolean values -/

noncomputable section
namespace LeanTrominoes.CompletionPattern.IBricks

set_option maxHeartbeats 2000000

/-- Boolean values are indexed by the microcell just below each connector. -/
def booleanMicroOwner (value : Cell → Bool) (c : Cell) : Cell :=
  let i : Cell := (c.1 / 18,c.2 / 27)
  let x := c.1 % 18
  if c.2 % 27 = 0 ∧
      (if x = 5 then value i = false else if x = 14 then value i = true else x < 9)
  then aboveMicro i else i

/-- The assigned microcell always contains the pixel. -/
theorem boolean_owner_contains (value : Cell → Bool) (c : Cell) :
    c ∈ microRegion (booleanMicroOwner value c) := by
  unfold booleanMicroOwner
  dsimp only
  split_ifs <;> rw [mem_microRegion] <;> dsimp [aboveMicro] <;> unfold MemberAt <;> omega

/-- True assigns the left connector pixel below and the right one above;
false reverses these two assignments. -/
theorem boolean_owner_portal (value : Cell → Bool) (i : Cell) (right : Bool) :
    booleanMicroOwner value (portalCell i right) =
      if value i = right then aboveMicro i else i := by
  have base : ((portalCell i right).1 / 18,(portalCell i right).2 / 27) = i := by
    cases right <;> apply Prod.ext <;> dsimp [portalCell] <;> omega
  have y : (portalCell i right).2 % 27 = 0 := by dsimp [portalCell]; omega
  have x : (portalCell i right).1 % 18 = if right then 14 else 5 := by
    cases right <;> dsimp [portalCell] <;> omega
  unfold booleanMicroOwner
  rw [base,y,x]
  cases right <;> cases h : value i <;> simp [h]

/-- A group retains exactly the pixels whose assigned microcell it owns. -/
def booleanGroupRegion (value : Cell → Bool) (s : Finset Cell) : Finset Cell :=
  (groupRegion s).filter fun c => booleanMicroOwner value c ∈ s

/-- Every interior pixel is retained, independently of the Boolean values. -/
theorem boolean_group_core (value : Cell → Bool) (s : Finset Cell) :
    groupRegion s \ groupBoundary s ⊆ booleanGroupRegion value s := by
  intro c hc
  exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hc).1,
    micro_in_group hc (boolean_owner_contains value c)⟩

/-- Any Boolean connector assignment partitions the plane among subbricks. -/
theorem boolean_groups_partition (palette : Cell → Fin 24) (value : Cell → Bool) (c : Cell) :
    ∃! o : Occurrence palette, c ∈ booleanGroupRegion value (groupAt o.location o.entry) := by
  obtain ⟨location,entry,he,owned⟩ := global_groups_cover palette (booleanMicroOwner value c)
  let o : Occurrence palette := ⟨location,entry,he⟩
  refine ⟨o,?_,?_⟩
  · exact Finset.mem_filter.mpr
      ⟨Finset.mem_biUnion.mpr ⟨booleanMicroOwner value c,owned,boolean_owner_contains value c⟩,owned⟩
  · intro other hc
    have ownOther := (Finset.mem_filter.mp hc).2
    have locationEq := group_locations_eq palette other.member he ownOther owned
    apply Occurrence.ext locationEq
    have entryEq : other.entry = entry := by
      have ho : other.entry ∈ layout (palette location) := by simpa only [locationEq] using other.member
      have own : booleanMicroOwner value c ∈ groupAt location other.entry := by rwa [locationEq] at ownOther
      exact group_entries_eq palette location ho he own owned
    exact entryEq

end LeanTrominoes.CompletionPattern.IBricks
