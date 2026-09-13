/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ThreeTranslationCompilerCorrect
import LeanTrominoes.Theorem55Hardness
import LeanTrominoes.Theorem55StripHardSourceCompiler

/-! # Plane and strip hardness for three translation-only polyominoes -/

namespace LeanTrominoes.ThreeTranslationPolyominoes
open Turing PeriodicCNFStripReduction PeriodicThreeDM.NormalizationCompiler

theorem plane_manyOne {α : Type} [Primcodable α] {source : α → Prop}
    (reduction : ContinuousPlanarReduction source) : source ≤₀ planeProblem := by
  refine ⟨fun a => Theorem55Compiler.compile
    (Theorem55Compiler.sourceInput (reduction.presentation a).toPlanarPresentation),
    Theorem55Compiler.compile_primrec.to_comp.comp (Theorem55Compiler.sourceInput_computable reduction),?_⟩
  intro a
  rw [compile_plane_correct]
  have h := (reduction.normalizedOrientationReduction.correct a).trans
    (Gadget.periodicRegion_correct_of_normalized .I Gadget.iOrientationBehaviorCorrect _
      (reduction.normalizedOrientationReduction.wellFormed a)
      (reduction.normalizedOrientationReduction.verticesSeparated a))
  change source a ↔ _
  change source a ↔ PeriodicTrominoTiling .I
    ((PeriodicThreeDM.NormalizationCompiler.compile (reduction.input a)).periodicRegion .I) at h
  rw [reduction.compile_eq a] at h
  simpa only [PeriodicTrominoTiling,Gadget.PeriodicOrthogonalDrawing.periodicRegion_fullRank,true_and] using h

theorem plane_coREHard : LeanWang.CoREHard planeProblem := by
  intro α _ source sourceCoRE
  exact (LeanWang.domino_problem_coRE_hard source sourceCoRE).trans
    (plane_manyOne PeriodicWangPlanarThreeDMReduction.continuousPlanarReduction)

theorem strip_PSPACEHard : Complexity.PSPACEHard Theorem55StripEncoding.finEncoding stripProblem := by
  intro Input encoding language membership
  obtain ⟨decider⟩ := membership
  let reduce := fun input => Theorem55StripUnary.compiledInput
    (directSparseCompiledTrominoStrip decider .I input)
  let compiler := TM2CompositionMachine.computableInPolyTime
    (Theorem55StripHardSource.compiler decider) Theorem55StripUnary.compiler
  apply Complexity.PolyTimeManyOneReducible.of_computableInPolyTime reduce ⟨compiler⟩
  intro input
  exact (directSparseCompiledTrominoStrip_correct decider .I Gadget.iOrientationBehaviorCorrect input).trans
    (compile_strip_correct _ (Theorem55StripHardSource.wellFormed decider input)).symm

end LeanTrominoes.ThreeTranslationPolyominoes
