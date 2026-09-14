/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ThreeTranslationPolycubeCompiler
import LeanTrominoes.Theorem55Hardness

/-! # Co-r.e. hardness for three translation-only connected polycubes -/

namespace LeanTrominoes.ThreeTranslationPolycubes

open PeriodicThreeDM.NormalizationCompiler

theorem space_manyOne {α : Type} [Primcodable α] {source : α → Prop}
    (reduction : ContinuousPlanarReduction source) : source ≤₀ spaceProblem := by
  refine ⟨fun a => TwoConnectedPolycubes.SpaceCompiler.compile
    (Theorem55Compiler.sourceInput (reduction.presentation a).toPlanarPresentation),
    TwoConnectedPolycubes.SpaceCompiler.compile_primrec.to_comp.comp (Theorem55Compiler.sourceInput_computable reduction), ?_⟩
  intro a
  rw [compile_space_correct]
  have h := (reduction.normalizedOrientationReduction.correct a).trans
    (Gadget.periodicRegion_correct_of_normalized .I Gadget.iOrientationBehaviorCorrect _
      (reduction.normalizedOrientationReduction.wellFormed a)
      (reduction.normalizedOrientationReduction.verticesSeparated a))
  change source a ↔ _
  change source a ↔ PeriodicTrominoTiling .I
    ((PeriodicThreeDM.NormalizationCompiler.compile (reduction.input a)).periodicRegion .I) at h
  rw [reduction.compile_eq a] at h
  simpa only [PeriodicTrominoTiling, Gadget.PeriodicOrthogonalDrawing.periodicRegion_fullRank, true_and] using h

theorem space_coREHard : LeanWang.CoREHard (spaceProblem) := by
  intro α _ source sourceCoRE
  exact (LeanWang.domino_problem_coRE_hard source sourceCoRE).trans
    (space_manyOne PeriodicWangPlanarThreeDMReduction.continuousPlanarReduction)

theorem slab_two_manyOne {α : Type} [Primcodable α] {source : α → Prop}
    (reduction : ContinuousPlanarReduction source) : source ≤₀ slabProblem 2 := by
  refine ⟨fun a => TwoConnectedPolycubes.SlabCompiler.compile
    (Theorem55Compiler.sourceInput (reduction.presentation a).toPlanarPresentation),
    TwoConnectedPolycubes.SlabCompiler.compile_primrec.to_comp.comp (Theorem55Compiler.sourceInput_computable reduction), ?_⟩
  intro a
  rw [compile_slab_two_correct]
  have h := (reduction.normalizedOrientationReduction.correct a).trans
    (Gadget.periodicRegion_correct_of_normalized .I Gadget.iOrientationBehaviorCorrect _
      (reduction.normalizedOrientationReduction.wellFormed a)
      (reduction.normalizedOrientationReduction.verticesSeparated a))
  change source a ↔ _
  change source a ↔ PeriodicTrominoTiling .I
    ((PeriodicThreeDM.NormalizationCompiler.compile (reduction.input a)).periodicRegion .I) at h
  rw [reduction.compile_eq a] at h
  simpa only [PeriodicTrominoTiling, Gadget.PeriodicOrthogonalDrawing.periodicRegion_fullRank, true_and] using h

theorem slab_two_coREHard : LeanWang.CoREHard (slabProblem 2) := by
  intro α _ source sourceCoRE
  exact (LeanWang.domino_problem_coRE_hard source sourceCoRE).trans
    (slab_two_manyOne PeriodicWangPlanarThreeDMReduction.continuousPlanarReduction)

theorem tall_slab_manyOne {height : Nat} (hh : 3 ≤ height) {α : Type} [Primcodable α] {source : α → Prop}
    (reduction : ContinuousPlanarReduction source) : source ≤₀ slabProblem height := by
  refine ⟨fun a => TwoConnectedPolycubes.TallSlabCompiler.compile height
    (Theorem55Compiler.sourceInput (reduction.presentation a).toPlanarPresentation),
    (TwoConnectedPolycubes.TallSlabCompiler.compile_primrec height).to_comp.comp (Theorem55Compiler.sourceInput_computable reduction), ?_⟩
  intro a
  rw [compile_tall_slab_correct hh]
  have h := (reduction.normalizedOrientationReduction.correct a).trans
    (Gadget.periodicRegion_correct_of_normalized .I Gadget.iOrientationBehaviorCorrect _
      (reduction.normalizedOrientationReduction.wellFormed a)
      (reduction.normalizedOrientationReduction.verticesSeparated a))
  change source a ↔ _
  change source a ↔ PeriodicTrominoTiling .I
    ((PeriodicThreeDM.NormalizationCompiler.compile (reduction.input a)).periodicRegion .I) at h
  rw [reduction.compile_eq a] at h
  simpa only [PeriodicTrominoTiling, Gadget.PeriodicOrthogonalDrawing.periodicRegion_fullRank, true_and] using h

theorem tall_slab_coREHard {height : Nat} (hh : 3 ≤ height) : LeanWang.CoREHard (slabProblem height) := by
  intro α _ source sourceCoRE
  exact (LeanWang.domino_problem_coRE_hard source sourceCoRE).trans
    (tall_slab_manyOne hh PeriodicWangPlanarThreeDMReduction.continuousPlanarReduction)


theorem slabs_coREHard (height : Nat) (hh : 1 < height) : LeanWang.CoREHard (slabProblem height) := by
  by_cases two : height = 2
  · subst height
    exact slab_two_coREHard
  · exact tall_slab_coREHard (by omega)

end LeanTrominoes.ThreeTranslationPolycubes
