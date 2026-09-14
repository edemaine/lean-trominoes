/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionIOrientationComputability
import LeanTrominoes.PeriodicWangPlanarThreeDMReduction

/-! # Co-r.e.-hardness of periodic I-tromino completion

The input is a finite motif of prescribed I-tromino placements and two
independent integer periods. A completing tiling is arbitrary, not necessarily
periodic. The reduction composes the established normalized-orientation
hardness theorem with the certified Boolean circuits and I-brick compiler.
-/

namespace LeanTrominoes.CompletionPattern.IBricks

/-- Every normalized orientation reduction compiles into a completion reduction. -/
theorem completion_manyOne_of_orientation
    {α : Type} [Primcodable α] {source : α → Prop}
    (reduction : Gadget.NormalizedOrientationReduction source) :
    source ≤₀ PeriodicTrominoPrefill.planeProblem .I := by
  refine ⟨fun input => compileDrawing (reduction.drawing input),
    compileDrawing_computable.comp reduction.drawing_computable,?_⟩
  intro input
  exact (reduction.correct input).trans
    (compileDrawing_correct _ (reduction.wellFormed input)).symm

/-- Completing a doubly periodic prefill by I-trominoes is co-r.e.-hard. -/
theorem iCompletion_coREHard :
    LeanWang.CoREHard (PeriodicTrominoPrefill.planeProblem .I) := by
  intro α _ source coRE
  obtain ⟨reduction⟩ := PeriodicWangPlanarThreeDMReduction.normalizedOrientationCoREHard source coRE
  exact completion_manyOne_of_orientation reduction

end LeanTrominoes.CompletionPattern.IBricks
