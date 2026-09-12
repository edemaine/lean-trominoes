/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Theorem55CompilerComputability
import LeanTrominoes.PeriodicWangPlanarThreeDMReduction

/-! # Co-r.e. hardness of the two-polyomino plane problem -/

namespace LeanTrominoes

open PeriodicThreeDM.NormalizationCompiler

namespace Theorem55Compiler

variable {α : Type} [Primcodable α] {source : α → Prop}

theorem sourceInput_computable (reduction : ContinuousPlanarReduction source) :
    Computable (fun a => sourceInput (reduction.presentation a).toPlanarPresentation) := by
  have data : Primrec (fun drawing : Gadget.PeriodicOrthogonalDrawing =>
      (6 * drawing.horizontalPeriod, drawing.periodicRegion .I)) :=
    Primrec.pair
      (Primrec.nat_mul.comp (Primrec.const 6) Gadget.periodicOrthogonalDrawing_horizontalPeriod_primrec)
      (Gadget.periodicRegion_primrec .I)
  apply (data.to_comp.comp reduction.normalizedOrientationReduction.drawing_computable).of_eq
  intro a
  change (6 * (PeriodicThreeDM.NormalizationCompiler.compile (reduction.input a)).horizontalPeriod,
    (PeriodicThreeDM.NormalizationCompiler.compile (reduction.input a)).periodicRegion .I) = _
  rw [reduction.compile_eq a]
  simp only [sourceInput, Theorem55Source.period, Gadget.PeriodicOrthogonalDrawing.horizontalPeriod,
    (reduction.presentation a).toPlanarPresentation.normalizedOrthogonalDrawing_periods.1]

theorem manyOne (reduction : ContinuousPlanarReduction source) : source ≤₀ Theorem55.planeProblem := by
  refine ⟨fun a => Theorem55Compiler.compile (sourceInput (reduction.presentation a).toPlanarPresentation),
    compile_primrec.to_comp.comp (sourceInput_computable reduction), ?_⟩
  intro a
  rw [compile_source_correct]
  have h := (reduction.normalizedOrientationReduction.correct a).trans
    (Gadget.periodicRegion_correct_of_normalized .I Gadget.iOrientationBehaviorCorrect _
      (reduction.normalizedOrientationReduction.wellFormed a)
      (reduction.normalizedOrientationReduction.verticesSeparated a))
  change source a ↔ _
  change source a ↔ PeriodicTrominoTiling .I
    ((PeriodicThreeDM.NormalizationCompiler.compile (reduction.input a)).periodicRegion .I) at h
  rw [reduction.compile_eq a] at h
  simpa only [PeriodicTrominoTiling, Gadget.PeriodicOrthogonalDrawing.periodicRegion_fullRank, true_and] using h

end Theorem55Compiler

theorem Theorem55.coREHard : LeanWang.CoREHard planeProblem := by
  intro α _ source sourceCoRE
  exact (LeanWang.domino_problem_coRE_hard source sourceCoRE).trans
    (Theorem55Compiler.manyOne PeriodicWangPlanarThreeDMReduction.continuousPlanarReduction)

end LeanTrominoes
