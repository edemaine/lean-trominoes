/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseAssignmentData
import LeanTrominoes.PeriodicCNFStripHorizontalProblem
import LeanTrominoes.PeriodicThreeDMNormalizationStripCellAssignmentBounds

/-! # Bounds for direct sparse normalization assignments -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseAssignmentBoundsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Every generated sparse assignment has nonnegative stored strip
coordinates. -/
theorem directSparseAssignmentsOfSymbols_nonnegative
    (symbols : List encoding.Γ) :
    ∀ assignment ∈ directSparseAssignmentsOfSymbols decider symbols,
      0 ≤ assignment.1.1 ∧ 0 ≤ assignment.1.2 := by
  intro assignment member
  let source := PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols
  let planar := (presentation source).toPlanarPresentation
  unfold directSparseAssignmentsOfSymbols
    directSparseNormalizationInputOfSymbols normalizationInput at member
  rw [PeriodicThreeDM.NormalizationCompiler.finalStripCellAssignments_inputOfPresentation]
    at member
  have horizontalBounds :=
    planar.finalStripCellAssignment_horizontal_bounds member
  have verticalBounds :=
    (presentation source).finalStripCellAssignment_vertical_interior
      (presentation source).problemWellFormed
      (problem_degreeTwoOrThree source)
      (problem_isOneDimensional source)
      (presentation_routePointsInExpandedVerticalBand source)
      member
  exact ⟨horizontalBounds.1, le_of_lt verticalBounds.1⟩

end PeriodicCNFStripReduction
end LeanTrominoes
