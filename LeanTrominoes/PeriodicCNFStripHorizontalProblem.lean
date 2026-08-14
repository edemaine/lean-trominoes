/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripPlanarReduction
import LeanTrominoes.PeriodicCNFStripProblemOneDimensional
import LeanTrominoes.PeriodicGridDrawingVerticalBand

/-!
# Horizontal final 3DM data for the local-periodic-CNF strip reduction
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance] sourceVariableDecidableEq

/-- The concrete source presentation's stored route points lie in the open
three-period vertical halo consumed by rectangular rasterization. -/
theorem presentation_routePointsInExpandedVerticalBand
    (source : PeriodicCNF Nat) :
    (presentation source).drawing.RoutePointsInExpandedVerticalBand := by
  apply PeriodicGridDrawing.routePointsInExpandedVerticalBand_of_expandedSquare
  apply PeriodicGridDrawing.routePointsInExpandedSquare_of_segmentEndpoints
  · exact
      PeriodicOrthocrossing.retainedOrderedFixedEightPolarityNormalizedPaddedContinuousPlanarPresentation_endpointBounds
        (sourceFormula source)
        (sourceFormula_isLocal source)
        (sourceFormula_widthAtMostThree source)
        (sourceFormula_occurrencesAtMostThree_canonicalBEq source)
        (sourceFormula_clausesNonempty source)
  · intro route routeMember
    exact PeriodicGridDrawing.route_length_ge_two_of_compatible_of_loopless
      (problem source).incidenceGraph (presentation source).drawing
      (presentation source).toPlanarPresentation.compatible
      ((problem source).incidenceGraph_edgesAreLoopless) routeMember

end PeriodicCNFStripReduction
end LeanTrominoes
