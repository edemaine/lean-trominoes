/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TallSlabCompilerCorrectness
import LeanTrominoes.Theorem55Hardness

/-! # Co-r.e. hardness for two connected polycubes in every fixed taller slab -/

namespace LeanTrominoes.TwoConnectedPolycubes

open PeriodicThreeDM.NormalizationCompiler

theorem TallSlabCompiler.manyOne {height : Nat} (hh : 3 ≤ height) {α : Type} [Primcodable α] {source : α → Prop}
    (reduction : ContinuousPlanarReduction source) : source ≤₀ slabProblem height := by
  refine ⟨fun a => TallSlabCompiler.compile height
    (Theorem55Compiler.sourceInput (reduction.presentation a).toPlanarPresentation),
    (TallSlabCompiler.compile_primrec height).to_comp.comp (Theorem55Compiler.sourceInput_computable reduction), ?_⟩
  intro a
  rw [TallSlabCompiler.compile_source_correct hh]
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
    (TallSlabCompiler.manyOne hh PeriodicWangPlanarThreeDMReduction.continuousPlanarReduction)

end LeanTrominoes.TwoConnectedPolycubes
