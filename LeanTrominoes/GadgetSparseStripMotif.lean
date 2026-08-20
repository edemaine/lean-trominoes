/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseStripData
import LeanTrominoes.PeriodicThreeDMNormalizationStripCellAssignmentBounds
import LeanTrominoes.PeriodicThreeDMNormalizationStripFinalAssignmentCollisionFreedom
import LeanTrominoes.PeriodicThreeDMNormalizationStripReadback

/-! # Sparse strip motif equivalence -/

namespace LeanTrominoes
namespace PeriodicThreeDM

open Gadget

/-- Collision freedom, assignment bounds, and exact lookup identify the
sparse assignment motif with the ordinary complete-raster gadget motif. -/
theorem ContinuousPlanarPresentation.mem_sparsePeriodicStrip_motif_iff
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (horizontal : problem.IsOneDimensional)
    (sourceInside : presentation.toPlanarPresentation.drawing
      |>.RoutePointsInExpandedVerticalBand)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (sourceSimple : ∀ route ∈ presentation.drawing.edgeRoutes,
      LocalIncidenceDrawing.RouteIsSimple route)
    (tromino : Tromino) (cell : Cell) :
    cell ∈ (presentation.sparsePeriodicStrip tromino).motif ↔
      cell ∈ (presentation.toPlanarPresentation
        |>.stripNormalizedOrthogonalDrawing.periodicStrip tromino).motif := by
  let planar := presentation.toPlanarPresentation
  let drawing := planar.stripNormalizedOrthogonalDrawing
  have periodEqual : drawing.horizontalPeriod =
      planar.finalNormalizationPeriod := by
    simpa only [Gadget.PeriodicOrthogonalDrawing.horizontalPeriod] using
      planar.stripNormalizedOrthogonalDrawing_periods.1
  have heightEqual : drawing.verticalPeriod = planar.finalStripHeight := by
    simpa only [Gadget.PeriodicOrthogonalDrawing.verticalPeriod] using
      planar.stripNormalizedOrthogonalDrawing_periods.2
  have keysNodup :
      (planar.finalStripCellAssignments.map Prod.fst).Nodup :=
    presentation.finalStripAssignmentsCollisionFree
      wellFormed degree separated sourceSimple
  have assignmentBounds : ∀ assignment ∈ planar.finalStripCellAssignments,
      0 ≤ assignment.1.1 ∧
        assignment.1.1 < (drawing.horizontalPeriod : Int) ∧
        0 ≤ assignment.1.2 ∧
        assignment.1.2 < (drawing.verticalPeriod : Int) := by
    intro assignment member
    have horizontalBounds :=
      planar.finalStripCellAssignment_horizontal_bounds member
    have verticalBounds :=
      presentation.finalStripCellAssignment_vertical_interior
        wellFormed degree horizontal sourceInside member
    change 0 < assignment.1.2 ∧
      assignment.1.2 <
        3 * planar.finalNormalizationPeriod at verticalBounds
    rw [periodEqual, heightEqual]
    unfold PlanarPresentation.finalStripHeight
    exact ⟨horizontalBounds.1, horizontalBounds.2,
      le_of_lt verticalBounds.1, by omega⟩
  have lookupRepresents : ∀ horizontal vertical,
      horizontal < drawing.horizontalPeriod →
      vertical < drawing.verticalPeriod →
      drawing.indexedCellType horizontal vertical =
        (planar.finalStripCellAssignments.lookup
          (((horizontal : Int), (vertical : Int)) : Cell)).getD .blank := by
    intro horizontalIndex verticalIndex horizontalValid verticalValid
    let horizontalFin : Fin drawing.horizontalPeriod :=
      ⟨horizontalIndex, horizontalValid⟩
    let verticalFin : Fin drawing.verticalPeriod :=
      ⟨verticalIndex, verticalValid⟩
    rw [drawing.indexedCellType_eq_get horizontalFin verticalFin]
    have readback := planar.stripNormalizedOrthogonalDrawing_get
      (horizontalFin, verticalFin)
    change drawing.get (horizontalFin, verticalFin) = _
    rw [readback]
    rfl
  rw [presentation.sparsePeriodicStrip_motif,
    PeriodicOrthogonalDrawing.periodicStrip_motif,
    ← drawing.computableExpandedMotif_eq tromino]
  exact Gadget.mem_sparseExpandedMotif_iff tromino drawing
    planar.finalStripCellAssignments keysNodup assignmentBounds
      lookupRepresents cell

end PeriodicThreeDM
end LeanTrominoes
