/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FootprintTiling

/-! # Extending a partial tromino tiling

Preplacements are geometric footprints, so equivalent symmetry descriptions
of the same tile are identified. A completion retains every preplaced tile.
-/

namespace LeanTrominoes.Tromino

/-- The cells already covered by the prescribed tiles. -/
def occupied (prescribed : Set (Finset Cell)) : Set Cell :=
  {c | ∃ f ∈ prescribed, c ∈ f}

/-- Legal, pairwise nonoverlapping trominoes contained in the target region. -/
structure IsPartialTiling (t : Tromino) (region : Set Cell)
    (prescribed : Set (Finset Cell)) : Prop where
  tilesInside : ∀ f ∈ prescribed, t.IsFootprint f ∧ ∀ c ∈ f, c ∈ region
  nonoverlap : ∀ f ∈ prescribed, ∀ g ∈ prescribed, ∀ c ∈ f, c ∈ g → f = g

/-- Some exact tiling extends the prescribed geometric tiles. -/
def Completable (t : Tromino) (region : Set Cell) (prescribed : Set (Finset Cell)) : Prop :=
  ∃ completed, t.IsFootprintTiling region completed ∧ prescribed ⊆ completed

theorem IsFootprintTiling.partial {t : Tromino} {region : Set Cell}
    {completed prescribed : Set (Finset Cell)}
    (h : t.IsFootprintTiling region completed) (sub : prescribed ⊆ completed) :
    t.IsPartialTiling region prescribed := by
  refine ⟨fun f hf => h.tilesInside f (sub hf),?_⟩
  intro f hf g hg c hc hc'
  obtain ⟨chosen,_,unique⟩ := h.uniqueCover c ((h.tilesInside f (sub hf)).2 c hc)
  exact (unique f ⟨sub hf,hc⟩).trans (unique g ⟨sub hg,hc'⟩).symm

/-- Remove the prescribed tiles from a full tiling; the remainder covers
exactly the cells that have not been prefilled. -/
theorem IsFootprintTiling.remove {t : Tromino} {region : Set Cell}
    {completed prescribed : Set (Finset Cell)}
    (h : t.IsFootprintTiling region completed) (sub : prescribed ⊆ completed) :
    t.IsFootprintTiling (region \ occupied prescribed) (completed \ prescribed) := by
  constructor
  · intro f hf
    refine ⟨(h.tilesInside f hf.1).1,?_⟩
    intro c hc
    refine ⟨(h.tilesInside f hf.1).2 c hc,?_⟩
    rintro ⟨g,hg,hgc⟩
    exact hf.2 ((h.partial (Set.Subset.refl completed)).nonoverlap
      g (sub hg) f hf.1 c hgc hc ▸ hg)
  · intro c hc
    obtain ⟨f,⟨hf,hfc⟩,unique⟩ := h.uniqueCover c hc.1
    refine ⟨f,⟨⟨hf,fun hp => hc.2 ⟨f,hp,hfc⟩⟩,hfc⟩,?_⟩
    intro g hg
    exact unique g ⟨hg.1.1,hg.2⟩

/-- A legal prefill can be completed precisely when its uncovered region
can be tiled. This applies to planes, strips, and finite gadget regions. -/
theorem completable_iff (t : Tromino) (region : Set Cell) (prescribed : Set (Finset Cell)) :
    t.Completable region prescribed ↔
      t.IsPartialTiling region prescribed ∧ t.Tileable (region \ occupied prescribed) := by
  constructor
  · rintro ⟨completed,h,sub⟩
    exact ⟨h.partial sub,(t.tileable_iff_exists_footprintTiling _).mpr ⟨_,h.remove sub⟩⟩
  · rintro ⟨prefill,tiled⟩
    obtain ⟨remaining,h⟩ := (t.tileable_iff_exists_footprintTiling _).mp tiled
    refine ⟨prescribed ∪ remaining,⟨?_,?_⟩,Set.subset_union_left⟩
    · intro f hf
      rcases hf with hp | hr
      · exact prefill.tilesInside f hp
      · exact ⟨(h.tilesInside f hr).1,fun c hc => ((h.tilesInside f hr).2 c hc).1⟩
    · intro c hc
      by_cases covered : c ∈ occupied prescribed
      · obtain ⟨f,hf,hfc⟩ := covered
        refine ⟨f,⟨Or.inl hf,hfc⟩,?_⟩
        intro g hg
        rcases hg.1 with hp | hr
        · exact prefill.nonoverlap g hp f hf c hg.2 hfc
        · exact False.elim (((h.tilesInside g hr).2 c hg.2).2 ⟨f,hf,hfc⟩)
      · obtain ⟨f,⟨hf,hfc⟩,unique⟩ := h.uniqueCover c ⟨hc,covered⟩
        refine ⟨f,⟨Or.inr hf,hfc⟩,?_⟩
        intro g hg
        rcases hg.1 with hp | hr
        · exact False.elim (covered ⟨g,hp,hg.2⟩)
        · exact unique g ⟨hr,hg.2⟩

/-- Empty prefill recovers ordinary tileability. -/
theorem completable_empty (t : Tromino) (region : Set Cell) :
    t.Completable region ∅ ↔ t.Tileable region := by
  rw [completable_iff]
  have empty : t.IsPartialTiling region ∅ := ⟨by simp,by simp⟩
  simp [occupied,empty]

end LeanTrominoes.Tromino
