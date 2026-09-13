/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedStripRightNeighbor
import LeanTrominoes.TilingRegionNormalization
import LeanTrominoes.TilingPairRegion

/-! # Normalizing a strip tiling and propagating a horizontal row -/

namespace LeanTrominoes.KeyedStripComplement
open KeyedPeriodicComplement (AdmissibleHoles referencePlacement)

theorem normalize {n : Nat} (hn : 96 ≤ n) (holes : Polyomino)
    (admissible : AdmissibleHoles n holes)
    (tiled : Tileable (pairTiles PlusRefinement.bumpy (tile n holes)) (horizontalStrip n)) :
    ∃ ps, IsTiling (pairTiles PlusRefinement.bumpy (tile n holes)) (horizontalStrip n) ps ∧
      referencePlacement ∈ ps := by
  obtain ⟨ps,ht⟩ := tiled
  obtain ⟨p,hp,hk⟩ := right_tile_occurs_region _ _ _ ps ht
    (PlusRefinement.bumpy_not_tileable_strip (by omega))
  have orient := placement_orientation hn holes admissible p.untag (by
    intro c hc
    apply ht.tilesInside p hp c
    simpa [Placement.cells,Placement.untag,pairTiles,hk] using hc)
  have invariant : ∀ c, Cell.add p.offset (p.symmetry.act c) ∈ horizontalStrip n ↔ c ∈ horizontalStrip n := by
    intro c
    rcases orient with ⟨hs,ho⟩ | ⟨hs,ho⟩ | ⟨hs,ho⟩ | ⟨hs,ho⟩ <;>
      change p.symmetry = _ at hs <;> change p.offset.2 = _ at ho <;>
      simp [horizontalStrip,hs,SquareSymmetry.act,Cell.add,ho] <;> omega
  obtain ⟨qs,hq,seed⟩ := ht.normalize_preserving p hp invariant
  exact ⟨qs,hq,by simpa [referencePlacement,hk] using seed⟩

theorem recenter_horizontal {ι : Type*} {tiles : ι → Polyomino} {ps : Set (Placement ι)}
    {n : Nat} (ht : IsTiling tiles (horizontalStrip n) ps) (x : Int) :
    IsTiling tiles (horizontalStrip n) {p | p.shift (x,0) ∈ ps} := by
  simpa [horizontalStrip,Cell.add] using ht.recenter_region (x,0)

theorem translated_neighbor {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (ps : Set (Placement Bool))
    (ht : IsTiling (pairTiles PlusRefinement.bumpy (tile n holes)) (horizontalStrip n) ps)
    (x : Int) (seed : (⟨true,.identity,(x,0)⟩ : Placement Bool) ∈ ps) :
    (⟨true,.identity,(x+n,0)⟩ : Placement Bool) ∈ ps := by
  have ref : referencePlacement ∈ {p : Placement Bool | p.shift (x,0) ∈ ps} := by
    simpa [referencePlacement,Placement.shift,Cell.add] using seed
  have next := right_neighbor hn period holes admissible _ (recenter_horizontal ht x) ref
  simpa [Placement.shift,Cell.add] using next

theorem ray_placements {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (ps : Set (Placement Bool))
    (ht : IsTiling (pairTiles PlusRefinement.bumpy (tile n holes)) (horizontalStrip n) ps)
    (seed : referencePlacement ∈ ps) (i : Nat) :
    (⟨true,.identity,((n : Int)*i,0)⟩ : Placement Bool) ∈ ps := by
  induction i with
  | zero => simpa [referencePlacement] using seed
  | succ i ih =>
    have next := translated_neighbor hn period holes admissible ps ht _ ih
    simpa [Nat.cast_add,mul_add] using next

end LeanTrominoes.KeyedStripComplement
