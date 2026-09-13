/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedPolycubeTallSlabOrientation
import LeanTrominoes.KeyedPolycubeTallSlabSmall
import LeanTrominoes.SlabCapObstruction
import LeanTrominoes.KeyedComplementRightNeighbor
import LeanTrominoes.PolycubeHorizontalLayers

/-! # Exact side-lock alignment under a variable-thickness solid cap -/

namespace LeanTrominoes.KeyedPeriodicComplement

private theorem disjoint_tall_slice {height : Nat} (hh : 3 ≤ height)
    (n : Nat) (holes : Polyomino) (p : VoxelPlacement Unit)
    (hd : Disjoint (tallSlabTile height n holes) (p.cells (fun _ => tallSlabTile height n holes)))
    (slice : Polyomino) (lift : ∀ c ∈ slice,
      (c,(slabBodyHeight height : Int)-2) ∈ p.cells (fun _ => tallSlabTile height n holes)) :
    Disjoint (tile n holes) slice := by
  apply Finset.disjoint_left.mpr
  intro c hc hs
  have body := slabBodyHeight_bounds hh
  exact Finset.disjoint_left.mp hd
    ((mem_tallSlabTile height n holes _).mpr (Or.inl ⟨hc,by omega⟩)) (lift c hs)

theorem tall_background_candidate {height n : Nat} (hh : 3 ≤ height)
    (wide : height < n) (hn : 96 ≤ n) (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (lock : Cell) (lockInside : lock ∈ square n) (expected : Placement Bool)
    (forcing : ∀ a : Placement Bool,
      lock ∈ a.cells (pairTiles PlusRefinement.bumpy (tile n holes)) →
      Disjoint (tile n holes) (a.cells (pairTiles PlusRefinement.bumpy (tile n holes))) → a = expected)
    (cap : ∀ a : Placement Unit, lock ∈ a.cells (fun _ => square n) →
      ¬ Disjoint (tile n holes) (a.cells (fun _ => square n)))
    (p : VoxelPlacement Unit)
    (inside : ∀ c ∈ p.cells (fun _ => tallSlabTile height n holes), c ∈ voxelSlab height)
    (covers : (lock,(slabBodyHeight height : Int)-2) ∈ p.cells (fun _ => tallSlabTile height n holes))
    (hd : Disjoint (tallSlabTile height n holes) (p.cells (fun _ => tallSlabTile height n holes))) :
    p.symmetry.axis = 0 ∧ p.symmetry.flip = false ∧ p.offset.2 = 0 ∧ p.toPlanar.tag true = expected := by
  have horizontal := tallSlabTile_horizontal hh wide holes p inside
  have heightEq := tallSlabTile_vertical_offset hh wide hn holes admissible p inside
  have body := slabBodyHeight_bounds hh
  rcases (tall_horizontal_cells height n holes p horizontal _).mp covers with h | h
  · have disjoint := disjoint_tall_slice hh n holes p hd (p.toPlanar.cells (fun _ => tile n holes))
      (fun c hc => (tall_horizontal_cells height n holes p horizontal _).mpr (Or.inl ⟨hc,h.2⟩))
    have planar := forcing (p.toPlanar.tag true) h.1 disjoint
    have unflipped : p.symmetry.flip = false := by
      cases hf : p.symmetry.flip
      · rfl
      · have height' : p.offset.2 = (height : Int)-1 := by simpa [hf] using heightEq
        have ref : (lock,(height : Int)-1) ∈ tallSlabTile height n holes :=
          (mem_tallSlabTile height n holes _).mpr (Or.inr ⟨lockInside,by omega⟩)
        have hit : (lock,(height : Int)-1) ∈ p.cells (fun _ => tallSlabTile height n holes) := by
          apply (tall_horizontal_cells height n holes p horizontal _).mpr
          exact Or.inl ⟨h.1,by simp [sourceHeight,hf,height']; omega⟩
        exact False.elim (Finset.disjoint_left.mp hd ref hit)
    exact ⟨horizontal,unflipped,by simpa [unflipped] using heightEq,planar⟩
  · have disjoint := disjoint_tall_slice hh n holes p hd (p.toPlanar.cells (fun _ => square n))
      (fun c hc => (tall_horizontal_cells height n holes p horizontal _).mpr (Or.inr ⟨hc,h.2⟩))
    exact False.elim (cap p.toPlanar h.1 disjoint)

def tallSlabReference : VoxelPlacement Bool := referencePlacement.toVoxel

theorem tallSlabReference_cells (height n : Nat) (holes : Polyomino) :
    tallSlabReference.cells (tallSlabFamily height n holes) = tallSlabTile height n holes := by
  simp [tallSlabReference,referencePlacement,Placement.toVoxel,VoxelPlacement.cells,
    tallSlabFamily,Polycube.pairTiles,CubeSymmetry.act,CubeSymmetry.cycle,
    SquareSymmetry.act,Voxel.add,Cell.add]

private theorem tall_neighbor_of_lock {height n : Nat} (hh : 3 ≤ height)
    (wide : height < n) (hn : 96 ≤ n) (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (lock : Cell) (lockInside : lock ∈ square n) (outside : lock ∉ tile n holes)
    (expected : Placement Bool)
    (forcing : ∀ a : Placement Bool,
      lock ∈ a.cells (pairTiles PlusRefinement.bumpy (tile n holes)) →
      Disjoint (tile n holes) (a.cells (pairTiles PlusRefinement.bumpy (tile n holes))) → a = expected)
    (cap : ∀ a : Placement Unit, lock ∈ a.cells (fun _ => square n) →
      ¬ Disjoint (tile n holes) (a.cells (fun _ => square n)))
    (small : ∀ p : VoxelPlacement Unit,
      (∀ c ∈ p.cells (fun _ => TwoConnectedPolycubes.slabSmall height), c ∈ voxelSlab height) →
      (lock,(slabBodyHeight height : Int)-2) ∈ p.cells (fun _ => TwoConnectedPolycubes.slabSmall height) →
      ¬ Disjoint (tallSlabTile height n holes) (p.cells (fun _ => TwoConnectedPolycubes.slabSmall height)))
    (placements : Set (VoxelPlacement Bool))
    (tiling : IsVoxelTiling (tallSlabFamily height n holes) (voxelSlab height) placements)
    (seed : tallSlabReference ∈ placements) : expected.toVoxel ∈ placements := by
  have body := slabBodyHeight_bounds hh
  obtain ⟨p,hp,hc⟩ := tiling.exists_cover (c := (lock,(slabBodyHeight height : Int)-2)) (by
    change 0 ≤ (slabBodyHeight height : Int)-2 ∧ (slabBodyHeight height : Int)-2 < height
    omega)
  have distinct : tallSlabReference ≠ p := by
    rintro rfl
    rw [tallSlabReference_cells,mem_tallSlabTile] at hc
    rcases hc with h | h
    · exact outside h.1
    · omega
  have hd := tiling.disjoint_cells seed hp distinct
  rw [tallSlabReference_cells] at hd
  have inside := tiling.tilesInside p hp
  cases hk : p.kind with
  | false =>
    have eq : p.cells (tallSlabFamily height n holes) = p.untag.cells (fun _ => TwoConnectedPolycubes.slabSmall height) := by
      simp [VoxelPlacement.cells,VoxelPlacement.untag,tallSlabFamily,Polycube.pairTiles,hk]
    rw [eq] at hc hd inside
    exact False.elim (small p.untag inside hc hd)
  | true =>
    have eq : p.cells (tallSlabFamily height n holes) = p.untag.cells (fun _ => tallSlabTile height n holes) := by
      simp [VoxelPlacement.cells,VoxelPlacement.untag,tallSlabFamily,Polycube.pairTiles,hk]
    rw [eq] at hc hd inside
    obtain ⟨horizontal,unflipped,hz,planar⟩ := tall_background_candidate hh wide hn holes admissible
      lock lockInside expected forcing cap p.untag inside hc hd
    have he : p.toPlanar = expected := by
      simpa [VoxelPlacement.toPlanar,VoxelPlacement.untag,Placement.tag,hk] using planar
    rw [← he,p.toVoxel_toPlanar horizontal unflipped hz]
    exact hp

theorem tall_slab_vertical_neighbor {height n : Nat} (hh : 3 ≤ height)
    (wide : height < n) (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (placements : Set (VoxelPlacement Bool))
    (tiling : IsVoxelTiling (tallSlabFamily height n holes) (voxelSlab height) placements)
    (seed : tallSlabReference ∈ placements) :
    (⟨true,.identity,(0,-(n : Int))⟩ : Placement Bool).toVoxel ∈ placements := by
  apply tall_neighbor_of_lock hh wide hn holes admissible (2,3) (by simp [mem_square]; omega) ?_ _
    (vertical_candidate hn period holes admissible) (square_cannot_fill_vertical_lock hn holes admissible)
    (tall_small_cannot_fill_vertical_lock hh hn holes admissible) placements tiling seed
  intro hc
  have h := tile_upper hn holes hc
  simp [KeyCornerArithmetic.upper,KeyCornerArithmetic.inBox,KeyCornerArithmetic.inVerticalLock,
    KeyCornerArithmetic.inHorizontalLock,KeyCornerArithmetic.inKey] at h
  omega

theorem tall_slab_right_neighbor {height n : Nat} (hh : 3 ≤ height)
    (wide : height < n) (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (placements : Set (VoxelPlacement Bool))
    (tiling : IsVoxelTiling (tallSlabFamily height n holes) (voxelSlab height) placements)
    (seed : tallSlabReference ∈ placements)
    : (⟨true,.identity,((n : Int),0)⟩ : Placement Bool).toVoxel ∈ placements := by
  apply tall_neighbor_of_lock hh wide hn holes admissible ((n : Int)-4,2) (by simp [mem_square]; omega) ?_ _
    (right_candidate hn period holes admissible) (square_cannot_fill_right_lock hn holes admissible)
    (tall_small_cannot_fill_right_lock hh hn period holes admissible) placements tiling seed
  intro hc
  have h := tile_upper hn holes hc
  simp [KeyCornerArithmetic.upper,KeyCornerArithmetic.inBox,KeyCornerArithmetic.inVerticalLock,
    KeyCornerArithmetic.inHorizontalLock,KeyCornerArithmetic.inKey] at h
  omega

end LeanTrominoes.KeyedPeriodicComplement
