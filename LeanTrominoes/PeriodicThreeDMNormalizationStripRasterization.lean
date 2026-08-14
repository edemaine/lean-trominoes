/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationRasterization

/-!
# Rectangular strip rasterization of normalized periodic 3DM

Unlike the square-torus rasterizer, this compiler reduces only the horizontal
coordinate modulo the final period.  It reflects and shifts the geometric
vertical coordinate into a `3P + 1`-row rectangle, leaving rows `0` and `3P`
available as blank seams.
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- Store a geometric point in the horizontally periodic, vertically open
three-period raster. -/
def stripRasterLocation (period : Nat) (point : Cell) : Cell :=
  (point.1 % period, 2 * (period : Int) - point.2)

/-- Assign routing cells to the internal points of a route using the strip
raster location. -/
def stripRouteInteriorAssignments (period : Nat) (color : WireColor) :
    List Cell → List NormalizedCellAssignment
  | before :: current :: after :: rest =>
      (stripRasterLocation period current,
        routingCellTypeAt before current after color) ::
      stripRouteInteriorAssignments period color (current :: after :: rest)
  | _ => []
termination_by points => points.length

/-- Actual row count of the rectangular strip drawing, including its two
blank boundary rows. -/
def PlanarPresentation.finalStripHeight
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) : Nat :=
  3 * presentation.finalNormalizationPeriod + 1

/-- Final normalized vertices placed in the open strip raster. -/
def PlanarPresentation.finalStripVertexAssignments
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    List NormalizedCellAssignment :=
  problem.contractedGraph.vertices.map fun vertex =>
    (stripRasterLocation presentation.finalNormalizationPeriod
      (presentation.finalNormalizationPosition vertex),
      presentation.finalVertexCellType vertex)

/-- Final normalized route interiors placed in the open strip raster. -/
def PlanarPresentation.finalStripRouteAssignments
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    List NormalizedCellAssignment :=
  problem.contractedEdges.flatMap fun edge =>
    stripRouteInteriorAssignments presentation.finalNormalizationPeriod
      edge.color (presentation.finalNormalizationRoute edge)

/-- Prioritized nonblank assignments for the rectangular strip raster. -/
def PlanarPresentation.finalStripCellAssignments
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    List NormalizedCellAssignment :=
  presentation.finalStripVertexAssignments ++
    presentation.finalStripRouteAssignments

/-- Total strip-raster lookup with a blank fallback. -/
def PlanarPresentation.finalStripCellTypeAt
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (location : Cell) : OrthogonalCellType :=
  (presentation.finalStripCellAssignments.lookup location).getD .blank

/-- Row-major rectangular cell array of width `P` and height `3P + 1`. -/
def PlanarPresentation.finalStripCellTypes
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    List OrthogonalCellType :=
  rowMajorList presentation.finalStripHeight
    presentation.finalNormalizationPeriod fun horizontal vertical =>
      presentation.finalStripCellTypeAt (horizontal, vertical)

/-- Executable normalized drawing with horizontal period `P` and blank-seam
vertical period `3P + 1`. -/
def PlanarPresentation.stripNormalizedOrthogonalDrawing
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    PeriodicOrthogonalDrawing where
  horizontalPeriodPred := presentation.finalNormalizationPeriod - 1
  verticalPeriodPred := 3 * presentation.finalNormalizationPeriod
  cellTypes := presentation.finalStripCellTypes

/-- The rectangular compiler advertises exactly its intended positive width
and height. -/
theorem PlanarPresentation.stripNormalizedOrthogonalDrawing_periods
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    presentation.stripNormalizedOrthogonalDrawing.horizontalPeriodPred + 1 =
        presentation.finalNormalizationPeriod ∧
      presentation.stripNormalizedOrthogonalDrawing.verticalPeriodPred + 1 =
        presentation.finalStripHeight := by
  have positive := presentation.finalNormalizationPeriod_pos
  constructor
  · simp [PlanarPresentation.stripNormalizedOrthogonalDrawing,
      Nat.sub_add_cancel
        (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt positive))]
  · rfl

/-- The row-major strip compiler emits exactly one cell per rectangular
fundamental-domain position. -/
theorem PlanarPresentation.finalStripCellTypes_length
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    presentation.finalStripCellTypes.length =
      presentation.finalStripHeight *
        presentation.finalNormalizationPeriod := by
  unfold PlanarPresentation.finalStripCellTypes rowMajorList
  rw [List.length_flatMap]
  simp

end PeriodicThreeDM
end LeanTrominoes
