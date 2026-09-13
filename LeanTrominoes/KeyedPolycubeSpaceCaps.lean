/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedPolycubeSpaceGrid
import LeanTrominoes.KeyedPolycubeSpaceConnected
import LeanTrominoes.BumpyPolycubeConnected
import LeanTrominoes.PolycubeCapSeparation
import LeanTrominoes.SquareGridTiling

/-! # The complete background grid isolates the simulation between solid caps -/

namespace LeanTrominoes.KeyedPeriodicComplement

def spaceGrid (n : Nat) : Set (VoxelPlacement Bool) :=
  {p | ∃ q ∈ gridPlacements n, p = (q.tag true).toVoxel}

theorem space_grid_cap_cover {n : Nat} (hn : 0 < n) (holes : Polyomino)
    (c : Cell) (z : Int) (hz : z = -1 ∨ z = 3) :
    ∃ g ∈ spaceGrid n, (c,z) ∈ g.cells (spaceFamily n holes) := by
  obtain ⟨p,hp,hc⟩ := (square_grid_tiling hn).exists_cover (Set.mem_univ c)
  refine ⟨(p.tag true).toVoxel,⟨p,hp,rfl⟩,?_⟩
  have eq : ((p.tag true).toVoxel).cells (spaceFamily n holes) =
      p.toVoxel.cells (fun _ => spaceTile n holes) := rfl
  rw [eq,space_horizontal_cells n holes p.toVoxel rfl]
  exact Or.inr ⟨hc,by simpa [sourceHeight,Placement.toVoxel] using hz⟩

theorem space_nongrid_avoids_caps {n : Nat} (hn : 0 < n) (holes : Polyomino)
    (placements : Set (VoxelPlacement Bool))
    (tiling : IsVoxelTiling (spaceFamily n holes) Set.univ placements)
    (grid : ∀ p ∈ gridPlacements n, (p.tag true).toVoxel ∈ placements)
    (p : VoxelPlacement Bool) (hp : p ∈ placements) (nongrid : p ∉ spaceGrid n) :
    ∀ c ∈ p.cells (spaceFamily n holes), c.2 ≠ -1 ∧ c.2 ≠ 3 := by
  intro c hc
  have absent : ¬ (c.2 = -1 ∨ c.2 = 3) := by
    intro hz
    obtain ⟨g,⟨q,hq,eq⟩,hg⟩ := space_grid_cap_cover hn holes c.1 c.2 hz
    have member : g ∈ placements := eq ▸ grid q hq
    have distinct : p ≠ g := by rintro rfl; exact nongrid ⟨q,hq,eq⟩
    exact Finset.disjoint_left.mp (tiling.disjoint_cells hp member distinct) hc hg
  exact ⟨fun h => absent (Or.inl h),fun h => absent (Or.inr h)⟩

theorem space_nongrid_confined {n : Nat} (hn : 96 ≤ n) (holes : Polyomino)
    (admissible : AdmissibleHoles n holes) (placements : Set (VoxelPlacement Bool))
    (tiling : IsVoxelTiling (spaceFamily n holes) Set.univ placements)
    (grid : ∀ p ∈ gridPlacements n, (p.tag true).toVoxel ∈ placements)
    (p : VoxelPlacement Bool) (hp : p ∈ placements) (nongrid : p ∉ spaceGrid n)
    (a : Cell) (ha : (a,1) ∈ p.cells (spaceFamily n holes)) :
    ∀ c ∈ p.cells (spaceFamily n holes), 0 ≤ c.2 ∧ c.2 ≤ 2 := by
  have connected : (spaceFamily n holes p.kind).IsConnected := by
    cases hk : p.kind
    · exact Polycube.bumpyThree_connected
    · exact spaceTile_connected hn holes admissible
  exact p.confined_by_caps (spaceFamily n holes) connected
    (space_nongrid_avoids_caps (by omega) holes placements tiling grid p hp nongrid)
    (a,1) ha (by omega)

end LeanTrominoes.KeyedPeriodicComplement
