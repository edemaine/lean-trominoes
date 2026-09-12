/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TilingTranslation

/-! # Changing the origin of a tiled region -/

namespace LeanTrominoes

theorem IsTiling.recenter_region {ι : Type*} {tiles : ι → Polyomino} {region : Set Cell}
    {placements : Set (Placement ι)} (tiling : IsTiling tiles region placements)
    (offset : Cell) :
    IsTiling tiles {c | Cell.add offset c ∈ region} {p | p.shift offset ∈ placements} := by
  constructor
  · intro p hp c hc
    exact tiling.tilesInside (p.shift offset) hp (Cell.add offset c)
      ((Placement.mem_shift_cells tiles offset p c).mpr hc)
  · intro c hc
    obtain ⟨a, ⟨ha, covers⟩, unique⟩ := tiling.uniqueCover (Cell.add offset c) hc
    let p := a.shift (Cell.sub (0, 0) offset)
    have shifted : p.shift offset = a := Placement.shift_cancel offset a
    have member : p.shift offset ∈ placements := shifted ▸ ha
    have pc : c ∈ p.cells tiles := by
      apply (Placement.mem_shift_cells tiles offset p c).mp
      rwa [shifted]
    refine ⟨p, ⟨member, pc⟩, ?_⟩
    intro b hb
    apply Placement.shift_injective offset
    rw [shifted]
    exact unique (b.shift offset)
      ⟨hb.1, (Placement.mem_shift_cells tiles offset b c).mpr hb.2⟩

theorem Tileable.recenter_region {ι : Type*} {tiles : ι → Polyomino} {region : Set Cell}
    (tiled : Tileable tiles region) (offset : Cell) :
    Tileable tiles {c | Cell.add offset c ∈ region} := by
  obtain ⟨ps, ht⟩ := tiled
  exact ⟨_, ht.recenter_region offset⟩

theorem tileable_recenter_region_iff {ι : Type*} (tiles : ι → Polyomino)
    (region : Set Cell) (offset : Cell) :
    Tileable tiles {c | Cell.add offset c ∈ region} ↔ Tileable tiles region := by
  constructor
  · intro h
    have shifted := h.recenter_region (Cell.sub (0, 0) offset)
    have same : {c | Cell.add offset (Cell.add (Cell.sub (0, 0) offset) c) ∈ region} = region := by
      ext c
      have sum : Cell.add offset (Cell.add (Cell.sub (0, 0) offset) c) = c := by
        apply Prod.ext <;> dsimp [Cell.add, Cell.sub] <;> omega
      change _ ∈ region ↔ c ∈ region
      rw [sum]
    change Tileable tiles {c | Cell.add offset (Cell.add (Cell.sub (0, 0) offset) c) ∈ region} at shifted
    rwa [same] at shifted
  · exact fun h => h.recenter_region offset

end LeanTrominoes
