/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling

/-! # Exact tilings with restricted orientations -/

namespace LeanTrominoes

/-- Only placements satisfying `allowed` may be used. -/
def TileableWith {ι : Type*} (tiles : ι → Polyomino) (region : Set Cell)
    (allowed : Placement ι → Prop) : Prop :=
  ∃ placements, IsTiling tiles region placements ∧ ∀ p ∈ placements, allowed p

/-- Every tile is placed by translation alone. -/
def TranslationTileable {ι : Type*} (tiles : ι → Polyomino) (region : Set Cell) : Prop :=
  TileableWith tiles region (fun p => p.symmetry = .identity)

theorem TileableWith.tileable {ι : Type*} {tiles : ι → Polyomino} {region : Set Cell}
    {allowed : Placement ι → Prop} (h : TileableWith tiles region allowed) : Tileable tiles region :=
  ⟨h.choose,h.choose_spec.1⟩

/-- Replacing placements by copies with identical footprints preserves exact tilings.
The replacement need not be injective on unused or empty placements. -/
theorem IsTiling.map_cells {ι κ : Type*} {tiles : ι → Polyomino} {other : κ → Polyomino}
    {region : Set Cell} {placements : Set (Placement ι)}
    (h : IsTiling tiles region placements) (f : Placement ι → Placement κ)
    (same : ∀ p ∈ placements, (f p).cells other = p.cells tiles) :
    IsTiling other region (f '' placements) := by
  constructor
  · rintro q ⟨p,hp,rfl⟩ c hc
    exact h.tilesInside p hp c ((same p hp) ▸ hc)
  · intro c hc
    obtain ⟨p,⟨hp,hpc⟩,unique⟩ := h.uniqueCover c hc
    refine ⟨f p,⟨⟨p,hp,rfl⟩,by rwa [same p hp]⟩,?_⟩
    rintro q ⟨⟨r,hr,rfl⟩,hrc⟩
    exact congrArg f (unique r ⟨hr,by rwa [← same r hr]⟩)

theorem TileableWith.map_cells {ι κ : Type*} {tiles : ι → Polyomino} {other : κ → Polyomino}
    {region : Set Cell} {allowed : Placement ι → Prop} {allowedOther : Placement κ → Prop}
    (h : TileableWith tiles region allowed) (f : Placement ι → Placement κ)
    (same : ∀ p, allowed p → (f p).cells other = p.cells tiles)
    (legal : ∀ p, allowed p → allowedOther (f p)) :
    TileableWith other region allowedOther := by
  obtain ⟨placements,tiling,allowed⟩ := h
  refine ⟨f '' placements,tiling.map_cells f (fun p hp => same p (allowed p hp)),?_⟩
  rintro q ⟨p,hp,rfl⟩
  exact legal p (allowed p hp)

end LeanTrominoes
