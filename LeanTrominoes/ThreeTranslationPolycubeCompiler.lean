/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ThreeTranslationPolycubeForward
import LeanTrominoes.TwoConnectedPolycubesSpaceCompiler
import LeanTrominoes.TwoConnectedPolycubesSlabCompiler
import LeanTrominoes.TallSlabCompilerCorrectness

/-! # The connected-polycube compilers preserve translation-only tilings -/

namespace LeanTrominoes.ThreeTranslationPolycubes

theorem slabSmall_eq (height : Nat) :
    Polycube.extrude PlusRefinement.bumpy (slabLayers height) = TwoConnectedPolycubes.slabSmall height := by
  unfold slabLayers TwoConnectedPolycubes.slabSmall
  split_ifs <;> rfl

theorem space_forget (input : List Voxel) (h : spaceProblem input) : TwoConnectedPolycubes.spaceProblem input :=
  ⟨h.1,((translationTileable_iff _ _ _).mp h.2).tileable⟩

theorem slab_forget (height : Nat) (input : List Voxel) (h : slabProblem height input) :
    TwoConnectedPolycubes.slabProblem height input := by
  refine ⟨h.1,?_⟩
  have ht := ((translationTileable_iff _ _ _).mp h.2).tileable
  rwa [slabSmall_eq] at ht

private theorem prepared_tiling {source : PeriodicThreeDM} (presentation : source.PlanarPresentation)
    (h : Tromino.I.Tileable (presentation.normalizedOrthogonalDrawing.periodicRegion .I).carrier) :
    TileableBy PlusRefinement.bumpy (KeyedPeriodicComplement.holesRegion (3 * Theorem55Source.period presentation)
      (Theorem55Source.holes presentation)) := by
  rw [Theorem55Source.holes_carrier]
  exact (PlusRefinement.bumpy_tileable_refinement_iff _).mpr ((Theorem55Source.tileable_iff presentation).mpr h)

theorem compile_space_correct {source : PeriodicThreeDM} (presentation : source.PlanarPresentation) :
    spaceProblem (TwoConnectedPolycubes.SpaceCompiler.compile (Theorem55Compiler.sourceInput presentation)) ↔
      Tromino.I.Tileable (presentation.normalizedOrthogonalDrawing.periodicRegion .I).carrier := by
  constructor
  · intro h
    exact (TwoConnectedPolycubes.SpaceCompiler.compile_source_correct presentation).mp (space_forget _ h)
  · intro h
    have old := (TwoConnectedPolycubes.SpaceCompiler.compile_source_correct presentation).mpr h
    refine ⟨old.1,?_⟩
    apply (translationTileable_iff _ _ _).mpr
    rw [TwoConnectedPolycubes.SpaceCompiler.compile_source]
    exact space_restricted_of_holes (by have := Theorem55Source.period_large presentation; omega) _ (prepared_tiling presentation h)

theorem compile_slab_two_correct {source : PeriodicThreeDM} (presentation : source.PlanarPresentation) :
    slabProblem 2 (TwoConnectedPolycubes.SlabCompiler.compile (Theorem55Compiler.sourceInput presentation)) ↔
      Tromino.I.Tileable (presentation.normalizedOrthogonalDrawing.periodicRegion .I).carrier := by
  constructor
  · intro h
    exact (TwoConnectedPolycubes.SlabCompiler.compile_source_correct presentation).mp (slab_forget 2 _ h)
  · intro h
    have old := (TwoConnectedPolycubes.SlabCompiler.compile_source_correct presentation).mpr h
    refine ⟨old.1,?_⟩
    apply (translationTileable_iff _ _ _).mpr
    rw [TwoConnectedPolycubes.SlabCompiler.compile_source]
    exact slab_two_restricted_of_holes (by have := Theorem55Source.period_large presentation; omega) _ (prepared_tiling presentation h)

theorem compile_tall_slab_correct {height : Nat} (hh : 3 ≤ height)
    {source : PeriodicThreeDM} (presentation : source.PlanarPresentation) :
    slabProblem height (TwoConnectedPolycubes.TallSlabCompiler.compile height (Theorem55Compiler.sourceInput presentation)) ↔
      Tromino.I.Tileable (presentation.normalizedOrthogonalDrawing.periodicRegion .I).carrier := by
  constructor
  · intro h
    exact (TwoConnectedPolycubes.TallSlabCompiler.compile_source_correct hh presentation).mp (slab_forget height _ h)
  · intro h
    have old := (TwoConnectedPolycubes.TallSlabCompiler.compile_source_correct hh presentation).mpr h
    refine ⟨old.1,?_⟩
    apply (translationTileable_iff _ _ _).mpr
    rw [TwoConnectedPolycubes.TallSlabCompiler.compile_source,slabSmall_eq]
    have hn : 0 < 3 * Theorem55Source.period presentation := by
      have := Theorem55Source.period_large presentation
      omega
    apply tall_slab_restricted_of_holes hh (Nat.mul_pos (by omega) hn)
    rw [KeyedPeriodicComplement.repeatMask_carrier (by omega) hn]
    exact prepared_tiling presentation h

end LeanTrominoes.ThreeTranslationPolycubes
