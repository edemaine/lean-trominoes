/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TilingSymmetry
import LeanTrominoes.TilingRegionTranslation

/-! # Rigid changes of coordinates in arbitrary tiled regions -/

namespace LeanTrominoes

theorem IsTiling.reorient_region {ι : Type*} {tiles : ι → Polyomino}
    {region : Set Cell} {placements : Set (Placement ι)} (tiling : IsTiling tiles region placements)
    (s : SquareSymmetry) : IsTiling tiles {c | s.act c ∈ region} {p | p.orient s ∈ placements} := by
  constructor
  · intro p hp c hc
    exact tiling.tilesInside (p.orient s) hp (s.act c) ((Placement.mem_orient_cells tiles s p c).mpr hc)
  · intro c hc
    obtain ⟨a, ⟨ha, covers⟩, unique⟩ := tiling.uniqueCover (s.act c) hc
    let p := a.orient s.inverse
    have oriented : p.orient s = a := Placement.orient_cancel s a
    have member : p.orient s ∈ placements := oriented ▸ ha
    have pc : c ∈ p.cells tiles := by
      apply (Placement.mem_orient_cells tiles s p c).mp
      rwa [oriented]
    refine ⟨p, ⟨member, pc⟩, ?_⟩
    intro b hb
    apply Placement.orient_injective s
    rw [oriented]
    exact unique (b.orient s)
      ⟨hb.1, (Placement.mem_orient_cells tiles s b c).mpr hb.2⟩

/-- Normalize a selected placement whose affine frame preserves the region. -/
theorem IsTiling.normalize_preserving {ι : Type*} {tiles : ι → Polyomino}
    {region : Set Cell} {placements : Set (Placement ι)}
    (tiling : IsTiling tiles region placements) (p : Placement ι) (hp : p ∈ placements)
    (invariant : ∀ c, Cell.add p.offset (p.symmetry.act c) ∈ region ↔ c ∈ region) :
    ∃ ps, IsTiling tiles region ps ∧
      (⟨p.kind,.identity,(0,0)⟩ : Placement ι) ∈ ps := by
  have normalized := (tiling.recenter_region p.offset).reorient_region p.symmetry
  have eq : {c | Cell.add p.offset (p.symmetry.act c) ∈ region} = region := Set.ext invariant
  change IsTiling tiles {c | Cell.add p.offset (p.symmetry.act c) ∈ region}
    {q | (q.orient p.symmetry).shift p.offset ∈ placements} at normalized
  rw [eq] at normalized
  refine ⟨_,normalized,?_⟩
  have same : ((⟨p.kind,.identity,(0,0)⟩ : Placement ι).orient p.symmetry).shift p.offset = p := by
    apply Placement.ext
    · rfl
    · exact SquareSymmetry.compose_identity _
    · simp [Placement.shift,Placement.orient,SquareSymmetry.act_zero,Cell.add]
  change ((⟨p.kind,.identity,(0,0)⟩ : Placement ι).orient p.symmetry).shift p.offset ∈ placements
  rwa [same]

end LeanTrominoes
