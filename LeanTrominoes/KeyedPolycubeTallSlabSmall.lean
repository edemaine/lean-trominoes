/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedPolycubeTallSlabGeometry
import LeanTrominoes.BumpyPolycubeTwoLocks
import LeanTrominoes.PolycubeSpaceSmallCertificates
import LeanTrominoes.PolycubeRelativeObstruction

/-! # Uniform small-tile exclusions at the side locks of every taller slab -/

namespace LeanTrominoes.KeyedPeriodicComplement

theorem shifted_spaceTile_mem_tall {height : Nat} (hh : 3 ≤ height)
    (n : Nat) (holes : Polyomino) (c : Voxel) (hc : c ∈ spaceTile n holes)
    (nonnegative : 0 ≤ c.2 + (slabBodyHeight height : Int) - 3) :
    (c.1,c.2+(slabBodyHeight height : Int)-3) ∈ tallSlabTile height n holes := by
  have bounds := slabBodyHeight_bounds hh
  rw [mem_tallSlabTile]
  rcases (mem_spaceTile n holes c).mp hc with h | h
  · exact Or.inl ⟨h.1,by omega⟩
  · exact Or.inr ⟨h.1,by omega⟩

private theorem small_lock_obstruction {height : Nat} (hh : 3 ≤ height)
    (n : Nat) (holes : Polyomino) (lock : Cell) (offsets : Finset Voxel)
    (occupied : ∀ d ∈ offsets, Voxel.add (lock,1) d ∈ spaceTile n holes)
    (forced : ∀ s : CubeSymmetry, SpaceLock.ForcedOverlap
      (TwoConnectedPolycubes.slabSmall height) offsets s)
    (p : VoxelPlacement Unit)
    (inside : ∀ c ∈ p.cells (fun _ => TwoConnectedPolycubes.slabSmall height), c ∈ voxelSlab height)
    (covers : (lock,(slabBodyHeight height : Int)-2) ∈
      p.cells (fun _ => TwoConnectedPolycubes.slabSmall height)) :
    ¬ Disjoint (tallSlabTile height n holes)
      (p.cells (fun _ => TwoConnectedPolycubes.slabSmall height)) := by
  intro disjoint
  obtain ⟨q,hq,eq⟩ := (p.mem_cells_iff _ _).mp covers
  obtain ⟨d,hd,hit⟩ := forced p.symmetry q hq
  have candidate := p.cover_relative (fun _ => TwoConnectedPolycubes.slabSmall height)
    q (lock,(slabBodyHeight height : Int)-2) d eq hit
  have heightBound := (inside _ candidate).1
  have reference := shifted_spaceTile_mem_tall hh n holes (Voxel.add (lock,1) d)
    (occupied d hd) (by dsimp [Voxel.add] at *; omega)
  have ref : Voxel.add (lock,(slabBodyHeight height : Int)-2) d ∈ tallSlabTile height n holes := by
    convert reference using 1 <;> simp [Voxel.add] <;> omega
  exact Finset.disjoint_left.mp disjoint ref candidate

theorem tall_small_cannot_fill_vertical_lock {height n : Nat} (hh : 3 ≤ height)
    (hn : 96 ≤ n) (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (p : VoxelPlacement Unit)
    (inside : ∀ c ∈ p.cells (fun _ => TwoConnectedPolycubes.slabSmall height), c ∈ voxelSlab height)
    (covers : ((2,3),(slabBodyHeight height : Int)-2) ∈
      p.cells (fun _ => TwoConnectedPolycubes.slabSmall height)) :
    ¬ Disjoint (tallSlabTile height n holes)
      (p.cells (fun _ => TwoConnectedPolycubes.slabSmall height)) := by
  apply small_lock_obstruction hh n holes (2,3) SpaceLock.verticalOffsets
    (fun d hd => SpaceKeyArithmetic.lower_tile hn holes admissible (SpaceLock.vertical_witnesses hn hd))
    ?_ p inside covers
  intro s
  have two : height ≠ 2 := by omega
  by_cases three : height = 3
  · simpa [TwoConnectedPolycubes.slabSmall,two,three] using SpaceLock.small_two_at_vertical_lock s
  · simpa [TwoConnectedPolycubes.slabSmall,two,three] using SpaceLock.small_at_vertical_lock s

theorem tall_small_cannot_fill_right_lock {height n : Nat} (hh : 3 ≤ height)
    (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (p : VoxelPlacement Unit)
    (inside : ∀ c ∈ p.cells (fun _ => TwoConnectedPolycubes.slabSmall height), c ∈ voxelSlab height)
    (covers : (((n : Int)-4,2),(slabBodyHeight height : Int)-2) ∈
      p.cells (fun _ => TwoConnectedPolycubes.slabSmall height)) :
    ¬ Disjoint (tallSlabTile height n holes)
      (p.cells (fun _ => TwoConnectedPolycubes.slabSmall height)) := by
  apply small_lock_obstruction hh n holes ((n : Int)-4,2) SpaceLock.rightOffsets
    (fun d hd => SpaceKeyArithmetic.lower_tile hn holes admissible (SpaceLock.right_witnesses hn period hd))
    ?_ p inside covers
  intro s
  have two : height ≠ 2 := by omega
  by_cases three : height = 3
  · simpa [TwoConnectedPolycubes.slabSmall,two,three] using SpaceLock.small_two_at_right_lock s
  · simpa [TwoConnectedPolycubes.slabSmall,two,three] using SpaceLock.small_at_right_lock s

end LeanTrominoes.KeyedPeriodicComplement
