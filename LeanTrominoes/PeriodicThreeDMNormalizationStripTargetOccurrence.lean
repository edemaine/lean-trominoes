/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMOneDimensionalContraction
import LeanTrominoes.PeriodicThreeDMNormalizationStripTargetEndpointRasterization

/-!
# Target occurrences in a one-dimensional normalized strip
-/

namespace LeanTrominoes

namespace PeriodicThreeDM

/-- In a one-dimensional instance, a normalized routed target occurrence and
its base target vertex have the same rectangular strip location.  The target
offset may cross the horizontal period seam but has no vertical component. -/
theorem PlanarPresentation.stripRasterLocation_finalTargetOccurrence
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (horizontal : problem.IsOneDimensional)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges) :
    stripRasterLocation presentation.finalNormalizationPeriod
        (normalizeVertexPosition (presentation.normalizationTarget2 edge)) =
      stripRasterLocation presentation.finalNormalizationPeriod
        (presentation.finalNormalizationPosition
          edge.toPeriodicEdge.target) := by
  have verticalZero :=
    contractedEdge_offset_vertical_eq_zero horizontal edgeMember
  have offsetEquation : edge.toPeriodicEdge.offset =
      (edge.toPeriodicEdge.offset.1, 0) := by
    apply Prod.ext
    · rfl
    · exact verticalZero
  rw [presentation.finalTargetOccurrence_eq]
  rw [presentation.finalScaledPeriodTranslation_eq]
  rw [offsetEquation]
  rcases presentation.finalNormalizationPosition edge.toPeriodicEdge.target with
    ⟨targetX, targetY⟩
  apply Prod.ext
  · simp [stripRasterLocation, Cell.add, Cell.scale, Int.add_emod]
  · simp [stripRasterLocation, Cell.add, Cell.scale]

end PeriodicThreeDM
end LeanTrominoes
