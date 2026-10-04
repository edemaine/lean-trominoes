/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionIBrickEquivalence
import LeanTrominoes.FiniteICompletionGuards

/-! # Local connector extraction from guarded tile ownership -/
noncomputable section
namespace LeanTrominoes.CompletionPattern.IBricks.FiniteGuards
open IBricks
set_option maxHeartbeats 2000000

def PortalOwners (palette : Cell → Fin 24) (completed : Set (Finset Cell))
    (i : Cell) (right : Bool) : Prop :=
  ∀ f∈completed, portalCell i right∈f → ∃ location : Cell,
    ∃ entry∈layout (palette location), f⊆regionAt location entry

/-- Across a genuine subbrick seam, each connector cell is external to
exactly one of the two subbricks. Both states come from the same global tiling. -/
theorem portal_complement (palette : Cell → Fin 24) (i : Cell) (right : Bool)
    {below above : Cell} {a b : Atom × Cell}
    (ha : a ∈ layout (palette below)) (hb : b ∈ layout (palette above))
    (ownBelow : i ∈ groupAt below a) (ownAbove : aboveMicro i ∈ groupAt above b)
    (distinct : ¬ (below = above ∧ a = b))
    {completed : Set (Finset Cell)} (h : Tromino.I.IsFootprintTiling Set.univ completed)
    (owners : PortalOwners palette completed i right) :
    portalCell i right ∈ Tromino.outsideCells completed (regionAt below a) ↔
      portalCell i right ∉ Tromino.outsideCells completed (regionAt above b) := by
  have inA : portalCell i right ∈ regionAt below a := by
    change portalCell i right ∈ a.1.pattern.region.image (Cell.add (Cell.add (origin below) a.2))
    rw [← group_at_region palette below ha,portal_group_membership]
    exact Or.inl ownBelow
  have inB : portalCell i right ∈ regionAt above b := by
    change portalCell i right ∈ b.1.pattern.region.image (Cell.add (Cell.add (origin above) b.2))
    rw [← group_at_region palette above hb,portal_group_membership]
    exact Or.inr ownAbove
  obtain ⟨f,⟨hf,covers⟩,_⟩ := h.uniqueCover (portalCell i right) trivial
  rw [outside_iff_tile_not_contained h hf covers _ inA,
    outside_iff_tile_not_contained h hf covers _ inB]
  have exclusive : ¬ (f ⊆ regionAt below a ∧ f ⊆ regionAt above b) := by
    rintro ⟨left,right⟩
    exact distinct (tile_owner_unique palette (h.tilesInside f hf).1 ha hb left right)
  have either : f ⊆ regionAt below a ∨ f ⊆ regionAt above b := by
    obtain ⟨other,e,he,contained⟩ := owners f hf covers
    rcases portal_region_owners palette i right ha hb he ownBelow ownAbove (contained covers) with
      ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Or.inl contained
    · exact Or.inr contained
  tauto

theorem outside_above_owned {palette : Cell → Fin 24} {completed : Set (Finset Cell)}
    (h : Tromino.I.IsFootprintTiling Set.univ completed)
    (i : Cell) (right : Bool) (owners : PortalOwners palette completed i right) (o : Occurrence palette)
    (owned : aboveMicro i ∈ groupAt o.location o.entry) (absent : i ∉ groupAt o.location o.entry) :
    portalCell i right ∈ Tromino.outsideCells completed (regionAt o.location o.entry) ↔
      ¬ OutsideBelow palette completed i right := by
  have mine := micro_occurrence_owns palette i
  have distinct : ¬ ((microOccurrence palette i).location = o.location ∧
      (microOccurrence palette i).entry = o.entry) := by
    rintro ⟨hl,he⟩
    rw [hl,he] at mine
    exact absent mine
  have complement := portal_complement palette i right (microOccurrence palette i).member o.member
    mine owned distinct h owners
  change OutsideBelow palette completed i right ↔ _ at complement
  tauto


/-- Canonical states read one shared global connector, with complementary
outside conventions for the subbrick above and the subbrick below. -/
theorem canonical_port {palette : Cell → Fin 24} {completed : Set (Finset Cell)}
    (h : Tromino.I.IsFootprintTiling Set.univ completed)
    (o : Occurrence palette) (p : Cell) (hp : p ∈ o.entry.1.portCells) (right : Bool)
    (owners : PortalOwners palette completed (Cell.add (atomMicroOffset o.location o.entry) p) right) :
    portalCell p right ∈ outsideAt completed o.location o.entry ↔
      if p.2 = 0 then OutsideBelow palette completed (Cell.add (atomMicroOffset o.location o.entry) p) right
      else ¬ OutsideBelow palette completed (Cell.add (atomMicroOffset o.location o.entry) p) right := by
  rw [mem_outsideAt,← atom_micro_offset palette o.location o.member,← portal_translation]
  have localOwner := o.entry.1.port_ownership p hp
  by_cases top : p.2 = 0
  · rw [if_pos top] at localOwner ⊢
    exact (outside_below_owned completed _ right o ((group_at_mem o p).mpr localOwner.1)).symm
  · rw [if_neg top] at localOwner ⊢
    apply outside_above_owned h _ right owners o
    · rw [above_micro_translation]
      exact (group_at_mem o (aboveMicro p)).mpr localOwner.1
    · exact fun member => localOwner.2 ((group_at_mem o p).mp member)

end LeanTrominoes.CompletionPattern.IBricks.FiniteGuards
