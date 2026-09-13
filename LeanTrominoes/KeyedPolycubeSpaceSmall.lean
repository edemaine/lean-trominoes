/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeRelativeObstruction
import LeanTrominoes.PolycubeSpaceSmallCertificates

/-! # Small-tile exclusions at the actual full-space side locks -/

namespace LeanTrominoes.SpaceLock

private theorem small_obstructs (obstacle : Polycube) (p : VoxelPlacement Unit) (c : Voxel)
    (offsets : Finset Voxel) (forced : ForcedOverlap Polycube.bumpyThree offsets p.symmetry)
    (occupied : ∀ d ∈ offsets, Voxel.add c d ∈ obstacle)
    (covers : c ∈ p.cells (fun _ => Polycube.bumpyThree)) :
    ¬ Disjoint obstacle (p.cells (fun _ => Polycube.bumpyThree)) := by
  intro disjoint
  obtain ⟨q,hq,eq⟩ := (VoxelPlacement.mem_cells_iff p _ c).mp covers
  obtain ⟨d,hd,hit⟩ := forced q hq
  exact Finset.disjoint_left.mp disjoint (occupied d hd)
    (p.cover_relative (fun _ => Polycube.bumpyThree) q c d eq hit)

theorem small_cannot_fill_vertical_lock {n : Nat} (hn : 96 ≤ n) (holes : Polyomino)
    (admissible : KeyedPeriodicComplement.AdmissibleHoles n holes) (p : VoxelPlacement Unit)
    (covers : ((2,3),1) ∈ p.cells (fun _ => Polycube.bumpyThree)) :
    ¬ Disjoint (KeyedPeriodicComplement.spaceTile n holes) (p.cells (fun _ => Polycube.bumpyThree)) :=
  small_obstructs _ p _ verticalOffsets (small_at_vertical_lock p.symmetry)
    (fun d hd => SpaceKeyArithmetic.lower_tile hn holes admissible (vertical_witnesses hn hd)) covers

theorem small_cannot_fill_right_lock {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : KeyedPeriodicComplement.AdmissibleHoles n holes)
    (p : VoxelPlacement Unit)
    (covers : (((n : Int)-4,2),1) ∈ p.cells (fun _ => Polycube.bumpyThree)) :
    ¬ Disjoint (KeyedPeriodicComplement.spaceTile n holes) (p.cells (fun _ => Polycube.bumpyThree)) :=
  small_obstructs _ p _ rightOffsets (small_at_right_lock p.symmetry)
    (fun d hd => SpaceKeyArithmetic.lower_tile hn holes admissible (right_witnesses hn period hd)) covers

end LeanTrominoes.SpaceLock
