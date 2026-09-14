/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrominoCompletion

/-! # Recovering local completion states from a global tiling -/

namespace LeanTrominoes.Tromino

def containedTiles (completed : Set (Finset Cell)) (region : Finset Cell) : Set (Finset Cell) :=
  {f | f ∈ completed ∧ f ⊆ region}

theorem IsFootprintTiling.restrict {t : Tromino} {global : Set Cell}
    {completed : Set (Finset Cell)} (h : t.IsFootprintTiling global completed)
    (region : Finset Cell) :
    t.IsFootprintTiling (occupied (containedTiles completed region))
      (containedTiles completed region) := by
  constructor
  · intro f hf
    exact ⟨(h.tilesInside f hf.1).1,fun c hc => ⟨f,hf,hc⟩⟩
  · rintro c ⟨f,hf,hfc⟩
    obtain ⟨chosen,_,unique⟩ := h.uniqueCover c ((h.tilesInside f hf.1).2 c hfc)
    refine ⟨f,⟨hf,hfc⟩,?_⟩
    intro g hg
    exact (unique g ⟨hg.1.1,hg.2⟩).trans (unique f ⟨hf.1,hfc⟩).symm

/-- If every tile meeting the interior stays within the local region, a
full tiling induces a completion obtained by deleting only boundary cells. -/
theorem IsFootprintTiling.local_completion {t : Tromino} {global : Set Cell}
    {completed : Set (Finset Cell)} (h : t.IsFootprintTiling global completed)
    (region boundary : Finset Cell) (prescribed : Set (Finset Cell))
    (regionInside : (region : Set Cell) ⊆ global)
    (retained : prescribed ⊆ completed)
    (prescribedInside : ∀ f ∈ prescribed, f ⊆ region)
    (noCrossing : ∀ f ∈ completed, ∀ c ∈ f,
      c ∈ region \ boundary → f ⊆ region) :
    ∃ outside : Finset Cell, outside ⊆ boundary ∧
      t.Completable (region \ outside : Finset Cell) prescribed := by
  classical
  let selected := containedTiles completed region
  let outside := region.filter fun c => c ∉ occupied selected
  have carrier : (↑(region \ outside) : Set Cell) = occupied selected := by
    ext c
    constructor
    · intro hc
      have notOutside := (Finset.mem_sdiff.mp hc).2
      by_contra absent
      exact notOutside (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hc).1,absent⟩)
    · intro hc
      obtain ⟨f,hf,hfc⟩ := hc
      exact Finset.mem_sdiff.mpr ⟨hf.2 hfc,fun ho => (Finset.mem_filter.mp ho).2 ⟨f,hf,hfc⟩⟩
  refine ⟨outside,?_,?_⟩
  · intro c hc
    obtain ⟨inside,absent⟩ := Finset.mem_filter.mp hc
    by_contra notBoundary
    obtain ⟨f,⟨hf,hfc⟩,_⟩ := h.uniqueCover c (regionInside inside)
    exact absent ⟨f,⟨hf,noCrossing f hf c hfc (Finset.mem_sdiff.mpr ⟨inside,notBoundary⟩)⟩,hfc⟩
  · rw [carrier]
    exact ⟨selected,h.restrict region,fun f hf => ⟨retained hf,prescribedInside f hf⟩⟩

end LeanTrominoes.Tromino
