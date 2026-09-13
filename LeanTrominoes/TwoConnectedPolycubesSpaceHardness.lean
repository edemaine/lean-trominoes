/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TwoConnectedPolycubesSpaceCompiler
import LeanTrominoes.Theorem55Hardness

/-! # Co-r.e. hardness for two connected polycubes in a full space -/

namespace LeanTrominoes.TwoConnectedPolycubes

open PeriodicThreeDM.NormalizationCompiler

theorem SpaceCompiler.manyOne {α : Type} [Primcodable α] {source : α → Prop}
    (reduction : ContinuousPlanarReduction source) : source ≤₀ spaceProblem := by
  refine ⟨fun a => SpaceCompiler.compile
    (Theorem55Compiler.sourceInput (reduction.presentation a).toPlanarPresentation),
    SpaceCompiler.compile_primrec.to_comp.comp (Theorem55Compiler.sourceInput_computable reduction), ?_⟩
  intro a
  rw [SpaceCompiler.compile_source_correct]
  have h := (reduction.normalizedOrientationReduction.correct a).trans
    (Gadget.periodicRegion_correct_of_normalized .I Gadget.iOrientationBehaviorCorrect _
      (reduction.normalizedOrientationReduction.wellFormed a)
      (reduction.normalizedOrientationReduction.verticesSeparated a))
  change source a ↔ _
  change source a ↔ PeriodicTrominoTiling .I
    ((PeriodicThreeDM.NormalizationCompiler.compile (reduction.input a)).periodicRegion .I) at h
  rw [reduction.compile_eq a] at h
  simpa only [PeriodicTrominoTiling, Gadget.PeriodicOrthogonalDrawing.periodicRegion_fullRank, true_and] using h

theorem space_coREHard : LeanWang.CoREHard spaceProblem := by
  intro α _ source sourceCoRE
  exact (LeanWang.domino_problem_coRE_hard source sourceCoRE).trans
    (SpaceCompiler.manyOne PeriodicWangPlanarThreeDMReduction.continuousPlanarReduction)

end LeanTrominoes.TwoConnectedPolycubes
