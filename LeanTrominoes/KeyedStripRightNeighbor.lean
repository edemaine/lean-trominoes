/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedStripLockArithmetic

/-! # The right lock forces the actual neighboring Q tile -/

namespace LeanTrominoes.KeyedStripComplement

open KeyedPeriodicComplement (AdmissibleHoles rightWorldPatch rightLock mem_square
  bumpy_cannot_fill_right_world cells_source_iff referencePlacement reference_cells)

private theorem right_witness_lower {n : Nat} (hn : 96 ≤ n) {d : Cell}
    (hd : d ∈ KeyCornerArithmetic.rightOffsets) :
    lower n (Cell.add ((n : Int) - 4, 2) d) := by
  have table : KeyCornerArithmetic.rightOffsets =
      {(1, 0), (-9, 1), (-1, -1), (0, 13), (0, -2), (-1, 1), (1, -1)} := by decide
  rw [table] at hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [lower, KeyCornerArithmetic.inBox,
      KeyCornerArithmetic.inHorizontalLock,
      inKey, Cell.add] <;> omega

private theorem right_patch_lower {n : Nat} (hn : 96 ≤ n) {c : Cell}
    (hc : c ∈ rightWorldPatch n) : lower n c := by
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨box, outside⟩ := Finset.mem_sdiff.mp hb
  have bounds := (mem_square 5 b).mp box
  simp only [rightLock, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff] at outside
  unfold lower KeyCornerArithmetic.inBox
    KeyCornerArithmetic.inHorizontalLock inKey
  dsimp [Cell.add, SquareSymmetry.act]
  omega

private theorem right_lock_outside {n : Nat} (hn : 96 ≤ n) :
    ¬ upper n ((n : Int) - 4, 2) := by
  simp [upper, KeyCornerArithmetic.inBox,
    KeyCornerArithmetic.inHorizontalLock,
    inKey]
  omega

/-- Local lock forcing, independent of a complete plane tiling. -/
theorem right_candidate {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes) (a : Placement Bool)
    (covers : ((n : Int) - 4, 2) ∈ a.cells (pairTiles PlusRefinement.bumpy (tile n holes)))
    (inside : ∀ c ∈ a.cells (pairTiles PlusRefinement.bumpy (tile n holes)), c ∈ horizontalStrip n)
    (disjoint : Disjoint (tile n holes)
      (a.cells (pairTiles PlusRefinement.bumpy (tile n holes)))) :
    a = (⟨true, .identity, ((n : Int), 0)⟩ : Placement Bool) := by
  cases hk : a.kind with
  | false =>
    have eq : a.cells (pairTiles PlusRefinement.bumpy (tile n holes)) =
        a.untag.cells (fun _ => PlusRefinement.bumpy) := by
      simp [Placement.cells, Placement.untag, pairTiles, hk]
    rw [eq] at covers disjoint
    have patch : rightWorldPatch n ⊆ tile n holes := fun c hc =>
      lower_tile hn holes admissible (right_patch_lower hn hc)
    exact False.elim (bumpy_cannot_fill_right_world n a.untag covers (disjoint.mono_left patch))
  | true =>
    have upper : upper n
        (KeyCornerArithmetic.source a.symmetry a.offset ((n : Int) - 4, 2)) := by
      have member := (cells_source_iff _ _ _).mp covers
      simp [pairTiles, hk] at member
      exact tile_upper n holes member
    have avoids : ∀ d ∈ KeyCornerArithmetic.rightOffsets,
        ¬ lower n
          (KeyCornerArithmetic.source a.symmetry a.offset (Cell.add ((n : Int) - 4, 2) d)) := by
      intro d hd source_lower
      have in_reference := lower_tile hn holes admissible (right_witness_lower hn hd)
      have in_candidate : Cell.add ((n : Int) - 4, 2) d ∈
          a.cells (pairTiles PlusRefinement.bumpy (tile n holes)) := by
        apply (cells_source_iff _ _ _).mpr
        simpa [pairTiles, hk] using
          lower_tile hn holes admissible source_lower
      exact (Finset.disjoint_left.mp disjoint) in_reference in_candidate
    have orientation := placement_orientation hn holes admissible a.untag (by
      intro c hc
      apply inside c
      simpa [Placement.cells,Placement.untag,pairTiles,hk] using hc)
    obtain ⟨hs, ho⟩ := right_match n (by omega) period a.symmetry a.offset orientation upper avoids
    exact Placement.ext hk hs ho

theorem strip_reference_cells (n : Nat) (holes : Polyomino) :
    referencePlacement.cells (pairTiles PlusRefinement.bumpy (tile n holes)) = tile n holes := by
  simp [referencePlacement, Placement.cells, pairTiles, SquareSymmetry.act, Cell.add]

/-- In an arbitrary mixed tiling containing the canonical reference Q, the
right lock forces another Q exactly one period to its right. -/
theorem right_neighbor {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (placements : Set (Placement Bool))
    (tiling : IsTiling (pairTiles PlusRefinement.bumpy (tile n holes)) (horizontalStrip n) placements)
    (reference_mem : referencePlacement ∈ placements) :
    (⟨true, .identity, ((n : Int), 0)⟩ : Placement Bool) ∈ placements := by
  obtain ⟨a, ha, covers⟩ := tiling.exists_cover (show ((n : Int) - 4, 2) ∈ horizontalStrip n from ⟨by omega,by omega⟩)
  have distinct : referencePlacement ≠ a := by
    rintro rfl
    rw [strip_reference_cells] at covers
    exact right_lock_outside hn (tile_upper n holes covers)
  have disjoint := tiling.disjoint_cells reference_mem ha distinct
  rw [strip_reference_cells] at disjoint
  have eq := right_candidate hn period holes admissible a covers (tiling.tilesInside a ha) disjoint
  rwa [← eq]

end LeanTrominoes.KeyedStripComplement
