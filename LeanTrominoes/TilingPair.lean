/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling

/-! # Combining two single-prototile tilings -/

namespace LeanTrominoes

/-- A pair of prototiles, with `false` selecting P and `true` selecting Q. -/
def pairTiles (p q : Polyomino) (kind : Bool) : Polyomino := if kind then q else p

namespace Placement

/-- Attach a tile-kind tag without changing the geometric placement. -/
def tag (kind : Bool) (p : Placement Unit) : Placement Bool :=
  ⟨kind, p.symmetry, p.offset⟩

/-- Forget the tag of a geometric placement. -/
def untag (p : Placement Bool) : Placement Unit := ⟨(), p.symmetry, p.offset⟩

@[simp] theorem untag_tag (kind : Bool) (p : Placement Unit) : (p.tag kind).untag = p := by
  apply Placement.ext
  · exact Subsingleton.elim _ _
  · rfl
  · rfl

@[simp] theorem tag_untag (p : Placement Bool) : p.untag.tag p.kind = p := rfl

theorem tag_cells (p q : Polyomino) (kind : Bool) (a : Placement Unit) :
    (a.tag kind).cells (pairTiles p q) = a.cells (fun _ => pairTiles p q kind) := rfl

end Placement

/-- Tag the two collections without changing their geometric placements. -/
def pairPlacements (ps qs : Set (Placement Unit)) : Set (Placement Bool) :=
  {a | if a.kind then a.untag ∈ qs else a.untag ∈ ps}

/-- The explicit union of tilings of a region and its complement. -/
theorem isTiling_pair_of_complement (p q : Polyomino) (region : Set Cell)
    (ps qs : Set (Placement Unit)) (pt : IsTiling (fun _ => p) region ps)
    (qt : IsTiling (fun _ => q) regionᶜ qs) :
    IsTiling (pairTiles p q) Set.univ (pairPlacements ps qs) := by
  classical
  let placements := pairPlacements ps qs
  change IsTiling (pairTiles p q) Set.univ placements
  refine ⟨fun _ _ _ _ => Set.mem_univ _, ?_⟩
  intro c _
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
        exact False.elim (qt.tilesInside other.untag hom c hcm hc)
  · obtain ⟨a, ⟨ha, hca⟩, unique⟩ := qt.uniqueCover c hc
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

/-- Tiling a region and its complement separately gives a two-tile plane tiling. -/
theorem tileable_pair_of_complement (p q : Polyomino) (region : Set Cell)
    (hp : TileableBy p region) (hq : TileableBy q regionᶜ) :
    Tileable (pairTiles p q) Set.univ := by
  obtain ⟨ps, pt⟩ := hp
  obtain ⟨qs, qt⟩ := hq
  exact ⟨pairPlacements ps qs, isTiling_pair_of_complement p q region ps qs pt qt⟩

/-- Removing a Q-background known to tile the complement recovers a P-tiling
of the remaining region. The background uses exactly the Q placements of
the supplied mixed tiling. -/
theorem tileable_left_of_background (p q : Polyomino) (region : Set Cell)
    (placements : Set (Placement Bool))
    (tiling : IsTiling (pairTiles p q) Set.univ placements)
    (background : IsTiling (fun _ : Unit => q) regionᶜ
      {a | a.tag true ∈ placements}) : TileableBy p region := by
  classical
  refine ⟨{a | a.tag false ∈ placements}, ?_, ?_⟩
  · intro a ha c hc
    by_contra outside
    obtain ⟨b, hb, hbc⟩ := background.exists_cover outside
    have distinct : a.tag false ≠ b.tag true := by
      intro eq
      have kinds := congrArg Placement.kind eq
      simp [Placement.tag] at kinds
    have disjoint := tiling.disjoint_cells ha hb distinct
    exact (Finset.disjoint_left.mp disjoint) hc hbc
  · intro c hc
    obtain ⟨a, ⟨ha, hca⟩, unique⟩ := tiling.uniqueCover c (Set.mem_univ c)
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
      exact False.elim (background.tilesInside a.untag mem c covers hc)

/-- If P alone cannot tile the plane, every mixed plane tiling uses Q. -/
theorem right_tile_occurs (p q : Polyomino) (placements : Set (Placement Bool))
    (tiling : IsTiling (pairTiles p q) Set.univ placements)
    (obstruction : ¬ TileableBy p Set.univ) :
    ∃ a ∈ placements, a.kind = true := by
  classical
  by_contra none
  have emptyBackground : IsTiling (fun _ : Unit => q) (Set.univ : Set Cell)ᶜ
      {a | a.tag true ∈ placements} := by
    constructor
    · intro a ha c _
      exact False.elim (none ⟨a.tag true, ha, rfl⟩)
    · intro c hc
      exact False.elim (hc (Set.mem_univ c))
  exact obstruction (tileable_left_of_background p q Set.univ placements tiling emptyBackground)

end LeanTrominoes
