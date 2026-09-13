/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ThreeTranslationPolyominoes
import LeanTrominoes.Theorem55Geometry

/-! # The keyed constructions use translations of the background tile -/

namespace LeanTrominoes.ThreeTranslationPolyominoes

private theorem pair_allowed (ps qs : Set (Placement Unit))
    (legal : ∀ q ∈ qs, q.symmetry = .identity) :
    ∀ p ∈ pairPlacements ps qs, Allowed p := by
  intro p hp kind
  have hq : p.untag ∈ qs := by simpa [pairPlacements,kind] using hp
  exact legal p.untag hq

theorem plane_of_source {n : Nat} (positive : 0 < n) (holes : Polyomino)
    (source : Set Cell)
    (carrier : KeyedPeriodicComplement.holesRegion n holes = PlusRefinement.region source)
    (tiled : Tromino.I.Tileable source) :
    TranslationTileable (tiles (KeyedPeriodicComplement.tile n holes)) Set.univ := by
  apply (translationTileable_iff _ _).mpr
  have small := (PlusRefinement.bumpy_tileable_refinement_iff source).mpr tiled
  rw [← carrier] at small
  obtain ⟨ps,hp⟩ := small
  refine ⟨pairPlacements ps (KeyedPeriodicComplement.gridPlacements n),
    isTiling_pair_of_complement _ _ _ _ _ hp (KeyedPeriodicComplement.grid_tiling positive holes),?_⟩
  exact pair_allowed _ _ (fun _ h => h.1)

theorem strip_of_source {n : Nat} (positive : 0 < n) (holes : Polyomino)
    (source : Set Cell)
    (carrier : KeyedStripComplement.holesRegion n holes = PlusRefinement.region source)
    (tiled : Tromino.I.Tileable source) :
    TranslationTileable (tiles (KeyedStripComplement.tile n holes)) (horizontalStrip n) := by
  apply (translationTileable_iff _ _).mpr
  have small := (PlusRefinement.bumpy_tileable_refinement_iff source).mpr tiled
  rw [← carrier] at small
  obtain ⟨ps,hp⟩ := small
  refine ⟨pairPlacements ps (KeyedStripComplement.gridPlacements n),
    isTiling_pair_of_difference _ _ _ _ (fun _ h => h.1) _ _ hp
      (KeyedStripComplement.grid_tiling positive holes),?_⟩
  exact pair_allowed _ _ (fun _ h => h.1)

theorem plane_iff_source {n : Nat} (large : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : KeyedPeriodicComplement.AdmissibleHoles n holes)
    (source : Set Cell)
    (carrier : KeyedPeriodicComplement.holesRegion n holes = PlusRefinement.region source) :
    TranslationTileable (tiles (KeyedPeriodicComplement.tile n holes)) Set.univ ↔
      Tromino.I.Tileable source := by
  constructor
  · intro h
    exact (Theorem55.pair_tileable_iff large period holes admissible source carrier).mp
      ((translationTileable_iff _ _).mp h).tileable
  · exact plane_of_source (by omega) holes source carrier

theorem strip_iff_source {n : Nat} (large : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : KeyedPeriodicComplement.AdmissibleHoles n holes)
    (source : Set Cell)
    (carrier : KeyedStripComplement.holesRegion n holes = PlusRefinement.region source) :
    TranslationTileable (tiles (KeyedStripComplement.tile n holes)) (horizontalStrip n) ↔
      Tromino.I.Tileable source := by
  constructor
  · intro h
    exact (KeyedStripComplement.pair_tileable_iff large period holes admissible source carrier).mp
      ((translationTileable_iff _ _).mp h).tileable
  · exact strip_of_source (by omega) holes source carrier

end LeanTrominoes.ThreeTranslationPolyominoes
