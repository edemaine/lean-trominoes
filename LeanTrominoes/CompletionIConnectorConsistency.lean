/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionIPortalGeometry

noncomputable section
namespace LeanTrominoes.CompletionPattern.IBricks

set_option maxHeartbeats 2000000

def regionAt (location : Cell) (entry : Atom × Cell) : Finset Cell :=
  entry.1.pattern.region.image (Cell.add (atomOffset location entry))

theorem outside_iff_tile_not_contained {completed : Set (Finset Cell)}
    (h : Tromino.I.IsFootprintTiling Set.univ completed) {f : Finset Cell} (hf : f ∈ completed)
    {c : Cell} (covers : c ∈ f) (region : Finset Cell) (inside : c ∈ region) :
    c ∈ Tromino.outsideCells completed region ↔ ¬ f ⊆ region := by
  simp only [Tromino.outsideCells,Finset.mem_filter]
  constructor
  · rintro ⟨_,absent⟩ contained
    exact absent ⟨f,⟨hf,contained⟩,covers⟩
  · intro notContained
    refine ⟨inside,?_⟩
    rintro ⟨g,⟨hg,contained⟩,hgc⟩
    have eq := (h.partial (Set.Subset.refl completed)).nonoverlap f hf g hg c covers hgc
    exact notContained (eq ▸ contained)

/-- Across a genuine subbrick seam, each connector cell is external to
exactly one of the two subbricks. Both states come from the same global tiling. -/
theorem portal_complement (palette : Cell → Fin 24) (i : Cell) (right : Bool)
    {below above : Cell} {a b : Atom × Cell}
    (ha : a ∈ layout (palette below)) (hb : b ∈ layout (palette above))
    (ownBelow : i ∈ groupAt below a) (ownAbove : aboveMicro i ∈ groupAt above b)
    (distinct : ¬ (below = above ∧ a = b))
    {completed : Set (Finset Cell)} (h : Tromino.I.IsFootprintTiling Set.univ completed)
    (retained : globalPrescribed palette ⊆ completed) :
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
    obtain ⟨other,e,he,contained⟩ := completed_tile_owner palette h retained hf
    rcases portal_region_owners palette i right ha hb he ownBelow ownAbove (contained covers) with
      ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Or.inl contained
    · exact Or.inr contained
  tauto

end LeanTrominoes.CompletionPattern.IBricks
