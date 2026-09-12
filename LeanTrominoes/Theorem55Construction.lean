/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Theorem55
import LeanTrominoes.BumpyTrominoConnected
import LeanTrominoes.BumpyTrominoObstruction
import LeanTrominoes.BumpyTrominoRefinement
import LeanTrominoes.KeyedPeriodicComplement
import LeanTrominoes.CornerKeyObstruction
import LeanTrominoes.KeyedComplementEnvelope
import LeanTrominoes.KeyedComplementRefinedExclusion
import LeanTrominoes.TilingPairNormalization
import LeanTrominoes.TilingPrescribedCompactness
import LeanTrominoes.KeyedComplementGridRecovery
import LeanTrominoes.KeyedComplementDisconnected

/-!
# Established parts of the two-polyomino construction

The fixed tile is connected, has 15 cells, and cannot tile the plane alone.
Cross refinement preserves I-tromino tileability exactly. The explicit keyed
complement supplies the forward implication for a square-periodic region.
The full target `Theorem55.planeStatement` is not proved by this module.
-/

namespace LeanTrominoes.Theorem55

/-- All three geometric properties required of the fixed small tile. -/
theorem smallTile_properties :
    PlusRefinement.bumpy.card = 15 ∧
    Polyomino.IsConnected PlusRefinement.bumpy ∧
    ¬ TileableBy PlusRefinement.bumpy Set.univ :=
  ⟨PlusRefinement.bumpy_card, PlusRefinement.bumpy_connected,
    PlusRefinement.bumpy_not_tileable_plane⟩

/-- The explicit pair tiles the plane whenever its periodic holes are P-tilable. -/
theorem pair_tileable_of_holes {n : Nat} (hn : 0 < n) (holes : Polyomino)
    (h : TileableBy PlusRefinement.bumpy
      (KeyedPeriodicComplement.holesRegion n holes)) :
    Tileable (pairTiles PlusRefinement.bumpy (KeyedPeriodicComplement.tile n holes))
      Set.univ :=
  tileable_pair_of_complement _ _ _ h
    ⟨KeyedPeriodicComplement.gridPlacements n, KeyedPeriodicComplement.grid_tiling hn holes⟩

/-- Forward reduction from an I-tromino region, once its refined periodic
carrier is expressed by the square mask `holes`. -/
theorem pair_tileable_of_tromino {n : Nat} (hn : 0 < n) (holes : Polyomino)
    (original : Set Cell)
    (carrier : KeyedPeriodicComplement.holesRegion n holes = PlusRefinement.region original)
    (h : Tromino.I.Tileable original) :
    Tileable (pairTiles PlusRefinement.bumpy (KeyedPeriodicComplement.tile n holes))
      Set.univ := by
  apply pair_tileable_of_holes hn holes
  rw [carrier, PlusRefinement.bumpy_tileable_refinement_iff]
  exact h

/-- Every mixed plane tiling contains at least one Q placement. -/
theorem background_occurs (q : Polyomino) (placements : Set (Placement Bool))
    (tiling : IsTiling (pairTiles PlusRefinement.bumpy q) Set.univ placements) :
    ∃ a ∈ placements, a.kind = true :=
  right_tile_occurs _ _ _ tiling PlusRefinement.bumpy_not_tileable_plane

/-- Once the actual Q placements are proved to tile the intended complement,
the mixed tiling recovers a tiling of the original I-tromino instance. -/
theorem recover_tromino_of_background (q : Polyomino) (original : Set Cell)
    (placements : Set (Placement Bool))
    (tiling : IsTiling (pairTiles PlusRefinement.bumpy q) Set.univ placements)
    (background : IsTiling (fun _ : Unit => q) (PlusRefinement.region original)ᶜ
      {a | a.tag true ∈ placements}) : Tromino.I.Tileable original :=
  (PlusRefinement.bumpy_tileable_refinement_iff original).mp
    (tileable_left_of_background _ _ _ placements tiling background)

end LeanTrominoes.Theorem55
