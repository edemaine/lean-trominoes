/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeSpaceSliceCertificates
import LeanTrominoes.KeyedPolycubeSpaceGeometry

/-! # Excluding unwanted tiles and orientations from the isolated middle slab -/

namespace LeanTrominoes

theorem KeyedPeriodicComplement.spaceTile_not_confined {n : Nat} (hn : 96 ≤ n)
    (holes : Polyomino) (p : VoxelPlacement Unit) :
    ¬ ∀ c ∈ p.cells (fun _ => spaceTile n holes), 0 ≤ c.2 ∧ c.2 ≤ 2 := by
  intro inside
  have probes : Polycube.spaceCapProbes ⊆ spaceTile n holes := by
    intro c hc
    simp only [Polycube.spaceCapProbes,Finset.mem_insert,Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl | rfl <;>
      apply (mem_spaceTile n holes _).mpr <;> right <;> constructor
    all_goals simp [mem_square] <;> omega
  obtain ⟨a,ha,b,hb,span⟩ := Polycube.spaceCapProbes_span p.symmetry
  have lo := inside _ ((p.mem_cells_iff _ _).mpr ⟨a,probes ha,rfl⟩)
  have hi := inside _ ((p.mem_cells_iff _ _).mpr ⟨b,probes hb,rfl⟩)
  dsimp [Voxel.add] at lo hi
  omega

theorem Polycube.bumpyThree_horizontal_of_cross_slice (p : VoxelPlacement Unit)
    (inside : ∀ c ∈ p.cells (fun _ => bumpyThree), 0 ≤ c.2 ∧ c.2 ≤ 2)
    (cross : ∀ c : Cell, (c,1) ∈ p.cells (fun _ => bumpyThree) →
      c.1 % 3 = 0 ∨ c.2 % 3 = 0) : p.symmetry.axis = 0 := by
  by_contra upright
  rcases bumpyThree_upright_square p.symmetry upright with ⟨a,ha,b,hb,span⟩ | ⟨r,hr,lo,hi,square⟩
  · have ha' := inside _ ((p.mem_cells_iff _ _).mpr ⟨a,ha,rfl⟩)
    have hb' := inside _ ((p.mem_cells_iff _ _).mpr ⟨b,hb,rfl⟩)
    dsimp [Voxel.add] at ha' hb'
    omega
  · have lift (c : Voxel) (hc : c ∈ bumpyThree.image p.symmetry.act) :
        Voxel.add p.offset c ∈ p.cells (fun _ => bumpyThree) := by
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hc
      exact (p.mem_cells_iff _ _).mpr ⟨q,hq,rfl⟩
    have lower := inside _ (lift _ lo)
    have upper := inside _ (lift _ hi)
    have height : p.offset.2 + r.2 = 1 := by dsimp [Voxel.add] at lower upper; omega
    have crosses (d : Cell) (hd : d ∈ PlusRefinement.unitSquare) :
        (p.offset.1.1 + r.1.1 + d.1) % 3 = 0 ∨
          (p.offset.1.2 + r.1.2 + d.2) % 3 = 0 := by
      have hc := lift _ (square d hd)
      have hc' : (Cell.add p.offset.1 (Cell.add r.1 d),1) ∈ p.cells (fun _ => bumpyThree) := by
        simpa only [Voxel.add,height] using hc
      simpa only [Cell.add,Int.add_assoc] using cross _ hc'
    have a := crosses (0,0) (by decide)
    have b := crosses (1,0) (by decide)
    have c := crosses (0,1) (by decide)
    have d := crosses (1,1) (by decide)
    dsimp only at a b c d
    omega

end LeanTrominoes
