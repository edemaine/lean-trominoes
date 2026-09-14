/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionOrientationComputability
import LeanTrominoes.PeriodicWangPlanarThreeDMReduction

/-! # Co-r.e.-hardness of periodic L-tromino completion

The input is a finite motif of prescribed L-tromino placements and two
independent integer periods. A completing tiling is arbitrary, not necessarily
periodic. The reduction composes the established normalized-orientation
hardness theorem with the certified Boolean circuits and L-brick compiler.
-/

namespace LeanTrominoes.CompletionPattern.LBricks

/-- Every normalized orientation reduction compiles into a completion reduction. -/
theorem completion_manyOne_of_orientation
    {α : Type} [Primcodable α] {source : α → Prop}
    (reduction : Gadget.NormalizedOrientationReduction source) :
    source ≤₀ PeriodicTrominoPrefill.planeProblem .L := by
  refine ⟨fun input => compileDrawing (reduction.drawing input),
    compileDrawing_computable.comp reduction.drawing_computable,?_⟩
  intro input
  exact (reduction.correct input).trans
    (compileDrawing_correct _ (reduction.wellFormed input)).symm

/-- Completing a doubly periodic prefill by L-trominoes is co-r.e.-hard. -/
theorem lCompletion_coREHard :
    LeanWang.CoREHard (PeriodicTrominoPrefill.planeProblem .L) := by
  intro α _ source coRE
  obtain ⟨reduction⟩ := PeriodicWangPlanarThreeDMReduction.normalizedOrientationCoREHard source coRE
  exact completion_manyOne_of_orientation reduction

end LeanTrominoes.CompletionPattern.LBricks
