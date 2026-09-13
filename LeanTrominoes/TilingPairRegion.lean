/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TilingPair

/-! # Combining and separating two tile families inside a containing region -/

namespace LeanTrominoes

theorem isTiling_pair_of_difference (p q : Polyomino) (whole region : Set Cell)
    (subset : region ⊆ whole)
    (ps qs : Set (Placement Unit)) (pt : IsTiling (fun _ => p) region ps)
    (qt : IsTiling (fun _ => q) (whole \ region) qs) :
    IsTiling (pairTiles p q) whole (pairPlacements ps qs) := by
  classical
  let placements := pairPlacements ps qs
  change IsTiling (pairTiles p q) whole placements
  refine ⟨?_, ?_⟩
  · intro a ha c hc
    cases hk : a.kind with
    | false =>
      have hom : a.untag ∈ ps := by simpa [placements,pairPlacements,hk] using ha
      have hcm : c ∈ a.untag.cells (fun _ => p) := by simpa [Placement.cells,Placement.untag,pairTiles,hk] using hc
      exact subset (pt.tilesInside a.untag hom c hcm)
    | true =>
      have hom : a.untag ∈ qs := by simpa [placements,pairPlacements,hk] using ha
      have hcm : c ∈ a.untag.cells (fun _ => q) := by simpa [Placement.cells,Placement.untag,pairTiles,hk] using hc
      exact (qt.tilesInside a.untag hom c hcm).1
  intro c hwhole
  by_cases hc : c ∈ region
  · obtain ⟨a, ⟨ha, hca⟩, unique⟩ := pt.uniqueCover c hc
    refine ⟨a.tag false, ⟨?_, hca⟩, ?_⟩
    · change (a.tag false).untag ∈ ps
      simpa only [Placement.untag_tag] using ha
    · rintro other ⟨ho, hco⟩
      cases hk : other.kind with
      | false =>
        have hom : other.untag ∈ ps := by simpa [placements, pairPlacements, hk] using ho
        have hcm : c ∈ other.untag.cells (fun _ => p) := by
          simpa [Placement.cells, Placement.untag, pairTiles, hk] using hco
        have eq := unique other.untag ⟨hom, hcm⟩
        apply Placement.ext hk
        · simpa only [Placement.untag, Placement.tag] using congrArg Placement.symmetry eq
        · simpa only [Placement.untag, Placement.tag] using congrArg Placement.offset eq
      | true =>
        have hom : other.untag ∈ qs := by simpa [placements, pairPlacements, hk] using ho
        have hcm : c ∈ other.untag.cells (fun _ => q) := by
          simpa [Placement.cells, Placement.untag, pairTiles, hk] using hco
        exact False.elim ((qt.tilesInside other.untag hom c hcm).2 hc)
  · obtain ⟨a, ⟨ha, hca⟩, unique⟩ := qt.uniqueCover c ⟨hwhole,hc⟩
    refine ⟨a.tag true, ⟨?_, hca⟩, ?_⟩
    · change (a.tag true).untag ∈ qs
      simpa only [Placement.untag_tag] using ha
    · rintro other ⟨ho, hco⟩
      cases hk : other.kind with
      | false =>
        have hom : other.untag ∈ ps := by simpa [placements, pairPlacements, hk] using ho
        have hcm : c ∈ other.untag.cells (fun _ => p) := by
          simpa [Placement.cells, Placement.untag, pairTiles, hk] using hco
        exact False.elim (hc (pt.tilesInside other.untag hom c hcm))
      | true =>
        have hom : other.untag ∈ qs := by simpa [placements, pairPlacements, hk] using ho
        have hcm : c ∈ other.untag.cells (fun _ => q) := by
          simpa [Placement.cells, Placement.untag, pairTiles, hk] using hco
        have eq := unique other.untag ⟨hom, hcm⟩
        apply Placement.ext hk
        · simpa only [Placement.untag, Placement.tag] using congrArg Placement.symmetry eq
        · simpa only [Placement.untag, Placement.tag] using congrArg Placement.offset eq

/-- Tiling a region and its complement separately gives a two-tile tiling of the containing region. -/
theorem tileable_pair_of_difference (p q : Polyomino) (whole region : Set Cell)
    (subset : region ⊆ whole)
    (hp : TileableBy p region) (hq : TileableBy q (whole \ region)) :
    Tileable (pairTiles p q) whole := by
  obtain ⟨ps, pt⟩ := hp
  obtain ⟨qs, qt⟩ := hq
  exact ⟨pairPlacements ps qs, isTiling_pair_of_difference p q whole region subset ps qs pt qt⟩

/-- Removing a Q-background known to tile the complement recovers a P-tiling
of the remaining region. The background uses exactly the Q placements of
the supplied mixed tiling. -/
theorem tileable_left_of_region_background (p q : Polyomino) (whole region : Set Cell)
    (subset : region ⊆ whole)
    (placements : Set (Placement Bool))
    (tiling : IsTiling (pairTiles p q) whole placements)
    (background : IsTiling (fun _ : Unit => q) (whole \ region)
      {a | a.tag true ∈ placements}) : TileableBy p region := by
  classical
  refine ⟨{a | a.tag false ∈ placements}, ?_, ?_⟩
  · intro a ha c hc
    by_contra outside
    obtain ⟨b, hb, hbc⟩ := background.exists_cover ⟨tiling.tilesInside (a.tag false) ha c hc,outside⟩
    have distinct : a.tag false ≠ b.tag true := by
      intro eq
      have kinds := congrArg Placement.kind eq
      simp [Placement.tag] at kinds
    have disjoint := tiling.disjoint_cells ha hb distinct
    exact (Finset.disjoint_left.mp disjoint) hc hbc
  · intro c hc
    obtain ⟨a, ⟨ha, hca⟩, unique⟩ := tiling.uniqueCover c (subset hc)
    cases hk : a.kind with
    | false =>
      have tagged : a.untag.tag false = a := by rw [← hk, Placement.tag_untag]
      have covers : c ∈ a.untag.cells (fun _ => p) := by
        simpa [Placement.cells, Placement.untag, pairTiles, hk] using hca
      refine ⟨a.untag, ⟨?_, covers⟩, ?_⟩
      · change a.untag.tag false ∈ placements
        rwa [tagged]
      · rintro other ⟨ho, hco⟩
        have eq := unique (other.tag false) ⟨ho, hco⟩
        simpa only [Placement.untag_tag] using congrArg Placement.untag eq
    | true =>
      have tagged : a.untag.tag true = a := by rw [← hk, Placement.tag_untag]
      have covers : c ∈ a.untag.cells (fun _ => q) := by
        simpa [Placement.cells, Placement.untag, pairTiles, hk] using hca
      have mem : a.untag.tag true ∈ placements := by rwa [tagged]
      exact False.elim ((background.tilesInside a.untag mem c covers).2 hc)

theorem right_tile_occurs_region (p q : Polyomino) (region : Set Cell) (placements : Set (Placement Bool))
    (tiling : IsTiling (pairTiles p q) region placements)
    (obstruction : ¬ TileableBy p region) :
    ∃ a ∈ placements, a.kind = true := by
  classical
  by_contra none
  have emptyBackground : IsTiling (fun _ : Unit => q) (region \ region)
      {a | a.tag true ∈ placements} := by
    constructor
    · intro a ha c _
      exact False.elim (none ⟨a.tag true, ha, rfl⟩)
    · intro c hc
      exact False.elim (hc.2 hc.1)
  exact obstruction (tileable_left_of_region_background p q region region (fun _ h => h) placements tiling emptyBackground)

end LeanTrominoes
