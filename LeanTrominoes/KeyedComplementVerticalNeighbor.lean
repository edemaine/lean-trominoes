/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedComplementEnvelope
import LeanTrominoes.KeyCornerArithmetic
import LeanTrominoes.CornerKeyObstruction
import LeanTrominoes.TilingPair

/-! # The vertical lock forces the actual neighboring Q tile -/

namespace LeanTrominoes.KeyedPeriodicComplement

private theorem source_cancel (s : SquareSymmetry) (offset c : Cell) :
    KeyCornerArithmetic.source s offset (Cell.add offset (s.act c)) = c := by
  cases s <;> apply Prod.ext <;>
    dsimp [KeyCornerArithmetic.source, SquareSymmetry.inverse, SquareSymmetry.act,
      Cell.add, Cell.sub] <;> omega

private theorem cancel_source (s : SquareSymmetry) (offset c : Cell) :
    Cell.add offset (s.act (KeyCornerArithmetic.source s offset c)) = c := by
  cases s <;> apply Prod.ext <;>
    dsimp [KeyCornerArithmetic.source, SquareSymmetry.inverse, SquareSymmetry.act,
      Cell.add, Cell.sub] <;> omega

theorem cells_source_iff {ι : Type*} (tiles : ι → Polyomino)
    (p : Placement ι) (c : Cell) :
    c ∈ p.cells tiles ↔ KeyCornerArithmetic.source p.symmetry p.offset c ∈ tiles p.kind := by
  rw [Placement.mem_cells_iff]
  constructor
  · rintro ⟨q, hq, rfl⟩
    rwa [source_cancel]
  · intro h
    exact ⟨_, h, cancel_source _ _ _⟩

private theorem vertical_witness_lower {n : Nat} (hn : 96 ≤ n) {d : Cell}
    (hd : d ∈ KeyCornerArithmetic.verticalOffsets) :
    KeyCornerArithmetic.lower n (Cell.add (2, 3) d) := by
  have table : KeyCornerArithmetic.verticalOffsets =
      {(1, 0), (0, 1), (-1, -1), (-1, 1), (4, -2), (-1, 0)} := by decide
  rw [table] at hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [KeyCornerArithmetic.lower, KeyCornerArithmetic.inBox,
      KeyCornerArithmetic.inVerticalLock, KeyCornerArithmetic.inHorizontalLock,
      KeyCornerArithmetic.inKey, Cell.add] <;> omega

private theorem vertical_patch_lower {n : Nat} (hn : 96 ≤ n) {c : Cell}
    (hc : c ∈ verticalPatch) : KeyCornerArithmetic.lower n c := by
  obtain ⟨hb, hv⟩ := Finset.mem_sdiff.mp hc
  have bounds := (mem_square 5 c).mp hb
  refine Or.inl ⟨?_, ?_, ?_, Or.inr ?_⟩
  · unfold KeyCornerArithmetic.inBox
    omega
  · exact fun h => hv ((verticalLock_iff _).mpr h)
  · unfold KeyCornerArithmetic.inHorizontalLock
    omega
  · exact ⟨Or.inl (by omega), Or.inl (by omega)⟩

private theorem vertical_lock_outside {n : Nat} (hn : 96 ≤ n) :
    ¬ KeyCornerArithmetic.upper n (2, 3) := by
  simp [KeyCornerArithmetic.upper, KeyCornerArithmetic.inBox,
    KeyCornerArithmetic.inVerticalLock, KeyCornerArithmetic.inHorizontalLock,
    KeyCornerArithmetic.inKey]
  omega

/-- The canonical reference copy of Q. -/
def referencePlacement : Placement Bool := ⟨true, .identity, (0, 0)⟩

theorem reference_cells (n : Nat) (holes : Polyomino) :
    referencePlacement.cells (pairTiles PlusRefinement.bumpy (tile n holes)) = tile n holes := by
  simp [referencePlacement, Placement.cells, pairTiles, SquareSymmetry.act, Cell.add]

/-- Local lock forcing, independent of a complete plane tiling. -/
theorem vertical_candidate {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes) (a : Placement Bool)
    (covers : (2, 3) ∈ a.cells (pairTiles PlusRefinement.bumpy (tile n holes)))
    (disjoint : Disjoint (tile n holes)
      (a.cells (pairTiles PlusRefinement.bumpy (tile n holes)))) :
    a = (⟨true, .identity, (0, -(n : Int))⟩ : Placement Bool) := by
  cases hk : a.kind with
  | false =>
    have eq : a.cells (pairTiles PlusRefinement.bumpy (tile n holes)) =
        a.untag.cells (fun _ => PlusRefinement.bumpy) := by
      simp [Placement.cells, Placement.untag, pairTiles, hk]
    rw [eq] at covers disjoint
    have patch : verticalPatch ⊆ tile n holes := fun c hc =>
      lower_tile hn holes admissible (vertical_patch_lower hn hc)
    exact False.elim (bumpy_cannot_fill_vertical_lock a.untag covers (disjoint.mono_left patch))
  | true =>
    have upper : KeyCornerArithmetic.upper n
        (KeyCornerArithmetic.source a.symmetry a.offset (2, 3)) := by
      have member := (cells_source_iff _ _ _).mp covers
      simp [pairTiles, hk] at member
      exact tile_upper hn holes member
    have avoids : ∀ d ∈ KeyCornerArithmetic.verticalOffsets,
        ¬ KeyCornerArithmetic.lower n
          (KeyCornerArithmetic.source a.symmetry a.offset (Cell.add (2, 3) d)) := by
      intro d hd source_lower
      have in_reference := lower_tile hn holes admissible (vertical_witness_lower hn hd)
      have in_candidate : Cell.add (2, 3) d ∈
          a.cells (pairTiles PlusRefinement.bumpy (tile n holes)) := by
        apply (cells_source_iff _ _ _).mpr
        simpa [pairTiles, hk] using
          lower_tile hn holes admissible source_lower
      exact (Finset.disjoint_left.mp disjoint) in_reference in_candidate
    obtain ⟨hs, ho⟩ := KeyCornerArithmetic.vertical_match n (by omega) period a.symmetry a.offset upper avoids
    exact Placement.ext hk hs ho

/-- In an arbitrary mixed tiling containing the canonical reference Q, the
vertical lock forces another Q exactly one period above it. -/
theorem vertical_neighbor {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (placements : Set (Placement Bool))
    (tiling : IsTiling (pairTiles PlusRefinement.bumpy (tile n holes)) Set.univ placements)
    (reference_mem : referencePlacement ∈ placements) :
    (⟨true, .identity, (0, -(n : Int))⟩ : Placement Bool) ∈ placements := by
  obtain ⟨a, ha, covers⟩ := tiling.exists_cover (Set.mem_univ (2, 3))
  have distinct : referencePlacement ≠ a := by
    rintro rfl
    rw [reference_cells] at covers
    exact vertical_lock_outside hn (tile_upper hn holes covers)
  have disjoint := tiling.disjoint_cells reference_mem ha distinct
  rw [reference_cells] at disjoint
  have eq := vertical_candidate hn period holes admissible a covers disjoint
  rwa [← eq]

end LeanTrominoes.KeyedPeriodicComplement
