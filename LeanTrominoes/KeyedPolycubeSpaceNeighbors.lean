/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedPolycubeSpaceLocks
import LeanTrominoes.KeyedPolycubeSpaceCanonical
import LeanTrominoes.PolycubeHorizontalLayers

/-! # Side neighbors in canonical full-space tilings -/

namespace LeanTrominoes.KeyedPeriodicComplement

def SpaceCanonical (placements : Set (VoxelPlacement Bool)) : Prop :=
  ∀ p ∈ placements, p.kind = true → p.symmetry.axis = 0 → p.symmetry.flip = false

def spaceReference : VoxelPlacement Bool := referencePlacement.toVoxel

theorem spaceReference_cells (n : Nat) (holes : Polyomino) :
    spaceReference.cells (spaceFamily n holes) = spaceTile n holes := by
  simp [spaceReference,referencePlacement,Placement.toVoxel,VoxelPlacement.cells,
    spaceFamily,Polycube.pairTiles,CubeSymmetry.act,CubeSymmetry.cycle,
    SquareSymmetry.act,Voxel.add,Cell.add]

private theorem neighbor_of_lock (n : Nat) (holes : Polyomino)
    (lock : Cell) (outside : lock ∉ tile n holes) (expected : Placement Bool)
    (small : ∀ p : VoxelPlacement Unit, (lock,1) ∈ p.cells (fun _ => Polycube.bumpyThree) →
      ¬ Disjoint (spaceTile n holes) (p.cells (fun _ => Polycube.bumpyThree)))
    (background : ∀ p : VoxelPlacement Unit, (lock,1) ∈ p.cells (fun _ => spaceTile n holes) →
      Disjoint (spaceTile n holes) (p.cells (fun _ => spaceTile n holes)) →
      p.symmetry.axis = 0 ∧ p.toPlanar.tag true = expected ∧
        p.offset.2 = if p.symmetry.flip then 2 else 0)
    (placements : Set (VoxelPlacement Bool))
    (tiling : IsVoxelTiling (spaceFamily n holes) Set.univ placements)
    (canonical : SpaceCanonical placements) (seed : spaceReference ∈ placements) :
    expected.toVoxel ∈ placements := by
  obtain ⟨p,hp,hc⟩ := tiling.exists_cover (c := (lock,1)) (Set.mem_univ _)
  have distinct : spaceReference ≠ p := by
    rintro rfl
    rw [spaceReference_cells,mem_spaceTile] at hc
    rcases hc with h | h
    · exact outside h.1
    · omega
  have hd := tiling.disjoint_cells seed hp distinct
  rw [spaceReference_cells] at hd
  cases hk : p.kind with
  | false =>
    have eq : p.cells (spaceFamily n holes) = p.untag.cells (fun _ => Polycube.bumpyThree) := by
      simp [VoxelPlacement.cells,VoxelPlacement.untag,spaceFamily,Polycube.pairTiles,hk]
    rw [eq] at hc hd
    exact False.elim (small p.untag hc hd)
  | true =>
    have eq : p.cells (spaceFamily n holes) = p.untag.cells (fun _ => spaceTile n holes) := by
      simp [VoxelPlacement.cells,VoxelPlacement.untag,spaceFamily,Polycube.pairTiles,hk]
    rw [eq] at hc hd
    obtain ⟨horizontal,planar,height⟩ := background p.untag hc hd
    have unflipped := canonical p hp hk horizontal
    have hz : p.offset.2 = 0 := by simpa [VoxelPlacement.untag,unflipped] using height
    have he : p.toPlanar = expected := by
      simpa [VoxelPlacement.toPlanar,VoxelPlacement.untag,Placement.tag,hk] using planar
    rw [← he,p.toVoxel_toPlanar horizontal unflipped hz]
    exact hp

theorem space_vertical_neighbor {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (placements : Set (VoxelPlacement Bool))
    (tiling : IsVoxelTiling (spaceFamily n holes) Set.univ placements)
    (canonical : SpaceCanonical placements) (seed : spaceReference ∈ placements) :
    (⟨true,.identity,(0,-(n : Int))⟩ : Placement Bool).toVoxel ∈ placements := by
  apply neighbor_of_lock n holes (2,3) ?_ _
    (SpaceLock.small_cannot_fill_vertical_lock hn holes admissible)
    (space_vertical_candidate hn period holes admissible) placements tiling canonical seed
  intro hc
  have h := tile_upper hn holes hc
  simp [KeyCornerArithmetic.upper,KeyCornerArithmetic.inBox,
    KeyCornerArithmetic.inVerticalLock,KeyCornerArithmetic.inHorizontalLock,
    KeyCornerArithmetic.inKey] at h
  omega

theorem space_right_neighbor {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (placements : Set (VoxelPlacement Bool))
    (tiling : IsVoxelTiling (spaceFamily n holes) Set.univ placements)
    (canonical : SpaceCanonical placements) (seed : spaceReference ∈ placements) :
    (⟨true,.identity,((n : Int),0)⟩ : Placement Bool).toVoxel ∈ placements := by
  apply neighbor_of_lock n holes ((n : Int)-4,2) ?_ _
    (SpaceLock.small_cannot_fill_right_lock hn period holes admissible)
    (space_right_candidate hn period holes admissible) placements tiling canonical seed
  intro hc
  have h := tile_upper hn holes hc
  simp [KeyCornerArithmetic.upper,KeyCornerArithmetic.inBox,
    KeyCornerArithmetic.inVerticalLock,KeyCornerArithmetic.inHorizontalLock,
    KeyCornerArithmetic.inKey] at h
  omega

end LeanTrominoes.KeyedPeriodicComplement
