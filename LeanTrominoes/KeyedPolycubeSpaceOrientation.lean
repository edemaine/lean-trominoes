/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeSpaceCapObstruction
import LeanTrominoes.PolycubeSpaceKeyCertificates
import LeanTrominoes.PolycubeRelativeObstruction
import LeanTrominoes.KeyedPolycubeSpaceKeys

/-! # Background tiles filling either side lock must be horizontal -/

namespace LeanTrominoes.SpaceLock

private theorem cap_mem {n : Nat} (holes : Polyomino) {c : Voxel} (h : inCap n c) :
    c ∈ KeyedPeriodicComplement.spaceTile n holes :=
  (KeyedPeriodicComplement.mem_spaceTile n holes c).mpr
    (Or.inr ⟨(KeyedPeriodicComplement.mem_square n c.1).mpr h.1,h.2⟩)

theorem background_horizontal {n : Nat} (hn : 96 ≤ n) (holes : Polyomino)
    (admissible : KeyedPeriodicComplement.AdmissibleHoles n holes)
    (p : VoxelPlacement Unit) (c : Voxel) (offsets : Finset Voxel)
    (keyCerts : ∀ s : CubeSymmetry, s.axis ≠ 0 →
      ForcedOverlap (keyPrism KeyedPeriodicComplement.verticalLock) offsets s ∧
        ForcedOverlap (keyPrism horizontalKey) offsets s)
    (occupied : ∀ d ∈ offsets, Voxel.add c d ∈ KeyedPeriodicComplement.spaceTile n holes)
    (caps : ∀ d ∈ capOffsets, inCap n (Voxel.add c d))
    (covers : c ∈ p.cells (fun _ => KeyedPeriodicComplement.spaceTile n holes))
    (disjoint : Disjoint (KeyedPeriodicComplement.spaceTile n holes)
      (p.cells (fun _ => KeyedPeriodicComplement.spaceTile n holes))) : p.symmetry.axis = 0 := by
  by_contra upright
  obtain ⟨q,hq,eq⟩ := (VoxelPlacement.mem_cells_iff p _ c).mp covers
  have shape := (KeyedPeriodicComplement.mem_spaceTile n holes q).mp hq
  have height : -1 ≤ q.2 ∧ q.2 ≤ 3 := by rcases shape with h | h <;> omega
  by_cases inside : q.1 ∈ KeyedPeriodicComplement.square n
  · obtain ⟨d,hd,hit⟩ := upright_cap_overlap n (by omega) p.symmetry upright q
      ((KeyedPeriodicComplement.mem_square n q.1).mp inside) height
    have member := cap_mem holes hit
    exact Finset.disjoint_left.mp disjoint (cap_mem holes (caps d hd))
      (p.cover_relative (fun _ => KeyedPeriodicComplement.spaceTile n holes) q c d eq member)
  · have body : q.1 ∈ KeyedPeriodicComplement.tile n holes ∧ 0 ≤ q.2 ∧ q.2 ≤ 2 := by
      rcases shape with h | h
      · exact h
      · exact False.elim (inside h.1)
    have upper := KeyedPeriodicComplement.tile_upper hn holes body.1
    have key : KeyCornerArithmetic.inKey n q.1 := by
      rcases upper with h | h
      · exact False.elim (inside ((KeyedPeriodicComplement.mem_square n q.1).mpr h.1))
      · exact h
    rcases key_cases n q key body.2 with ⟨r,hr,rfl⟩ | ⟨r,hr,rfl⟩
    · exact (keyCerts p.symmetry upright).1.obstructs
        (fun _ : Unit => KeyedPeriodicComplement.spaceTile n holes) p _ offsets
        ((0,n),0) r c hr (fun t ht => vertical_key_embed hn holes admissible ht)
        eq _ occupied disjoint
    · exact (keyCerts p.symmetry upright).2.obstructs
        (fun _ : Unit => KeyedPeriodicComplement.spaceTile n holes) p _ offsets
        ((0,0),0) r c hr (fun t ht => horizontal_key_embed hn holes admissible ht)
        eq _ occupied disjoint

theorem vertical_background_horizontal {n : Nat} (hn : 96 ≤ n) (holes : Polyomino)
    (admissible : KeyedPeriodicComplement.AdmissibleHoles n holes) (p : VoxelPlacement Unit)
    (covers : ((2,3),1) ∈ p.cells (fun _ => KeyedPeriodicComplement.spaceTile n holes))
    (disjoint : Disjoint (KeyedPeriodicComplement.spaceTile n holes)
      (p.cells (fun _ => KeyedPeriodicComplement.spaceTile n holes))) : p.symmetry.axis = 0 := by
  exact background_horizontal hn holes admissible p _ verticalOffsets
    (fun s h => ⟨vertical_key_at_vertical_lock s h, horizontal_key_at_vertical_lock s h⟩)
    (fun d hd => SpaceKeyArithmetic.lower_tile hn holes admissible (vertical_witnesses hn hd))
    (fun d hd => vertical_cap_witnesses hn hd) covers disjoint

theorem right_background_horizontal {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : KeyedPeriodicComplement.AdmissibleHoles n holes)
    (p : VoxelPlacement Unit)
    (covers : (((n : Int)-4,2),1) ∈ p.cells (fun _ => KeyedPeriodicComplement.spaceTile n holes))
    (disjoint : Disjoint (KeyedPeriodicComplement.spaceTile n holes)
      (p.cells (fun _ => KeyedPeriodicComplement.spaceTile n holes))) : p.symmetry.axis = 0 := by
  exact background_horizontal hn holes admissible p _ rightOffsets
    (fun s h => ⟨vertical_key_at_right_lock s h, horizontal_key_at_right_lock s h⟩)
    (fun d hd => SpaceKeyArithmetic.lower_tile hn holes admissible (right_witnesses hn period hd))
    (fun d hd => right_cap_witnesses hn hd) covers disjoint

end LeanTrominoes.SpaceLock
