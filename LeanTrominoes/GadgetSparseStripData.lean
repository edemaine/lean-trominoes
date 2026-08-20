/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseExpandedMotif
import LeanTrominoes.GadgetStripSubstitution
import LeanTrominoes.PeriodicThreeDMNormalizationStripAssignmentGeometry

/-! # Sparse strip-substitution data -/

namespace LeanTrominoes
namespace PeriodicThreeDM

open Gadget

/-- Every listed strip assignment has a horizontal coordinate in the chosen
fundamental period. -/
theorem PlanarPresentation.finalStripCellAssignment_horizontal_bounds
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {assignment : NormalizedCellAssignment}
    (member : assignment ∈ presentation.finalStripCellAssignments) :
    0 ≤ assignment.1.1 ∧
      assignment.1.1 < (presentation.finalNormalizationPeriod : Int) := by
  have locationMember :
      assignment.1 ∈ presentation.finalStripAssignmentLocations :=
    List.mem_map.mpr ⟨assignment, member, rfl⟩
  rw [presentation.finalStripAssignmentLocations_eq_map] at locationMember
  obtain ⟨point, _, locationEquality⟩ := List.mem_map.mp locationMember
  rw [← locationEquality]
  have periodPositive : (0 : Int) < presentation.finalNormalizationPeriod := by
    exact_mod_cast presentation.finalNormalizationPeriod_pos
  exact ⟨Int.emod_nonneg point.1 (ne_of_gt periodPositive),
    Int.emod_lt_of_pos point.1 periodPositive⟩

/-- Sparse assignment-order substitution, avoiding the blank-heavy complete
rectangular raster. -/
def ContinuousPlanarPresentation.sparsePeriodicStrip
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (tromino : Tromino) : PeriodicStrip where
  width := 6 * presentation.toPlanarPresentation.finalStripHeight
  period := 6 * presentation.toPlanarPresentation.finalNormalizationPeriod
  motif := Gadget.sparseExpandedMotif tromino
    presentation.toPlanarPresentation.finalStripCellAssignments

@[simp] theorem ContinuousPlanarPresentation.sparsePeriodicStrip_width
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (tromino : Tromino) :
    (presentation.sparsePeriodicStrip tromino).width =
      6 * presentation.toPlanarPresentation.finalStripHeight :=
  rfl

@[simp] theorem ContinuousPlanarPresentation.sparsePeriodicStrip_period
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (tromino : Tromino) :
    (presentation.sparsePeriodicStrip tromino).period =
      6 * presentation.toPlanarPresentation.finalNormalizationPeriod :=
  rfl

@[simp] theorem ContinuousPlanarPresentation.sparsePeriodicStrip_motif
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (tromino : Tromino) :
    (presentation.sparsePeriodicStrip tromino).motif =
      Gadget.sparseExpandedMotif tromino
        presentation.toPlanarPresentation.finalStripCellAssignments :=
  rfl

@[simp] theorem PeriodicOrthogonalDrawing.periodicStrip_motif
    (drawing : PeriodicOrthogonalDrawing) (tromino : Tromino) :
    (drawing.periodicStrip tromino).motif = drawing.expandedMotif tromino :=
  rfl

theorem ContinuousPlanarPresentation.sparsePeriodicStrip_width_eq_dense
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (tromino : Tromino) :
    (presentation.sparsePeriodicStrip tromino).width =
      (presentation.toPlanarPresentation
        |>.stripNormalizedOrthogonalDrawing.periodicStrip tromino).width := by
  rw [presentation.sparsePeriodicStrip_width,
    Gadget.PeriodicOrthogonalDrawing.periodicStrip_width]
  congr 1

theorem ContinuousPlanarPresentation.sparsePeriodicStrip_period_eq_dense
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (tromino : Tromino) :
    (presentation.sparsePeriodicStrip tromino).period =
      (presentation.toPlanarPresentation
        |>.stripNormalizedOrthogonalDrawing.periodicStrip tromino).period := by
  rw [presentation.sparsePeriodicStrip_period,
    Gadget.PeriodicOrthogonalDrawing.periodicStrip_period]
  congr 1

theorem ContinuousPlanarPresentation.sparsePeriodicStrip_inFundamentalDomain_iff
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (tromino : Tromino) (cell : Cell) :
    (presentation.sparsePeriodicStrip tromino).InFundamentalDomain cell ↔
      PeriodicStrip.InFundamentalDomain
        (presentation.toPlanarPresentation
          |>.stripNormalizedOrthogonalDrawing.periodicStrip tromino) cell := by
  unfold PeriodicStrip.InFundamentalDomain
  rw [presentation.sparsePeriodicStrip_width_eq_dense tromino,
    presentation.sparsePeriodicStrip_period_eq_dense tromino]

end PeriodicThreeDM
end LeanTrominoes
