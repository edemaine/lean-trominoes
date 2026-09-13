/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeHorizontalLayers
import LeanTrominoes.PolycubePair
import LeanTrominoes.BumpyPolycubeSlab
import LeanTrominoes.KeyedPolycubeSlabOrientation
import LeanTrominoes.TilingPair

/-! # Exact zero-layer footprints of mixed slab placements -/

namespace LeanTrominoes.KeyedPeriodicComplement

def slabFamily (n : Nat) (holes : Polyomino) : Bool → Polycube :=
  Polycube.pairTiles Polycube.bumpyOne (slabTile n holes)

def planarFamily (n : Nat) (holes : Polyomino) : Bool → Polyomino :=
  pairTiles PlusRefinement.bumpy (tile n holes)

theorem mixed_slab_horizontal {n : Nat} (hn : 96 ≤ n) (holes : Polyomino)
    (p : VoxelPlacement Bool)
    (inside : ∀ c ∈ p.cells (slabFamily n holes), c ∈ voxelSlab 2) :
    p.symmetry.axis = 0 := by
  cases hk : p.kind with
  | false =>
    apply Polycube.bumpyOne_horizontal p.untag
    intro c hc
    apply inside c
    simpa [VoxelPlacement.cells, VoxelPlacement.untag, slabFamily, Polycube.pairTiles, hk] using hc
  | true =>
    apply slabTile_horizontal (by omega : 3 ≤ n) holes p.untag
    intro c hc
    apply inside c
    simpa [VoxelPlacement.cells, VoxelPlacement.untag, slabFamily, Polycube.pairTiles, hk] using hc

theorem mixed_background_height {n : Nat} (hn : 96 ≤ n) (holes : Polyomino)
    (admissible : AdmissibleHoles n holes) (p : VoxelPlacement Bool) (hk : p.kind = true)
    (inside : ∀ c ∈ p.cells (slabFamily n holes), c ∈ voxelSlab 2) :
    p.offset.2 = if p.symmetry.flip then 1 else 0 := by
  apply slabTile_vertical_offset hn holes admissible p.untag
  intro c hc
  apply inside c
  simpa [VoxelPlacement.cells, VoxelPlacement.untag, slabFamily, Polycube.pairTiles, hk] using hc

theorem small_zero_slice (n : Nat) (holes : Polyomino) (p : VoxelPlacement Bool)
    (hk : p.kind = false) (horizontal : p.symmetry.axis = 0) (c : Cell) :
    (c, 0) ∈ p.cells (slabFamily n holes) ↔
      c ∈ p.toPlanar.cells (planarFamily n holes) ∧ 0 = p.offset.2 := by
  have he := p.horizontal_cells (fun _ : Bool => PlusRefinement.bumpy) horizontal (c, 0)
  simpa [VoxelPlacement.cells, slabFamily, Polycube.pairTiles, Polycube.bumpyOne,
    Placement.cells, VoxelPlacement.toPlanar, planarFamily, pairTiles, hk] using he

theorem background_zero_slice {n : Nat} (hn : 96 ≤ n) (holes : Polyomino)
    (admissible : AdmissibleHoles n holes) (p : VoxelPlacement Bool) (hk : p.kind = true)
    (inside : ∀ c ∈ p.cells (slabFamily n holes), c ∈ voxelSlab 2) (c : Cell) :
    (c, 0) ∈ p.cells (slabFamily n holes) ↔
      if p.symmetry.flip then c ∈ p.toPlanar.untag.cells (fun _ => square n)
      else c ∈ p.toPlanar.cells (planarFamily n holes) := by
  have horizontal := mixed_slab_horizontal hn holes p inside
  have height := mixed_background_height hn holes admissible p hk inside
  have he := p.horizontal_capped_cells (fun _ : Bool => tile n holes)
    (fun _ => square n) horizontal (c, 0)
  cases hf : p.symmetry.flip <;>
    simp only [hf, Bool.false_eq_true, ↓reduceIte] at height ⊢ <;>
    simpa [VoxelPlacement.cells, slabFamily, Polycube.pairTiles, slabTile, hk,
      Placement.cells, VoxelPlacement.toPlanar, Placement.untag, planarFamily, pairTiles,
      hf, height] using he

/-- Any footprint in the zero layer is disjoint from the reference Q body. -/
theorem disjoint_zero_slice (n : Nat) (holes : Polyomino) (p : VoxelPlacement Bool)
    (hd : Disjoint (slabTile n holes) (p.cells (slabFamily n holes)))
    (shape : Polyomino) (lift : ∀ c ∈ shape, (c, 0) ∈ p.cells (slabFamily n holes)) :
    Disjoint (tile n holes) shape := by
  rw [Finset.disjoint_left]
  intro c hc hs
  have href : (c, 0) ∈ slabTile n holes := by simp [slabTile, hc]
  exact (Finset.disjoint_left.mp hd) href (lift c hs)

end LeanTrominoes.KeyedPeriodicComplement
