/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirectionTranslation
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseStubData
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableStubData

/-! # Direction words of horizontal occurrence endpoint stubs -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- Finite coordinated variable-fan word before physical translation. -/
def horizontalOccurrenceVariableStubDirections
    (input : HorizontalOccurrenceColoredRouteInput) :
    List AxisDirection :=
  unitSubdivisionDirections
    (horizontalOccurrenceVariableCoordinatedRouteComputed input)

/-- Finite coordinated clause-fan word before physical translation. -/
def horizontalOccurrenceClauseStubDirections
    (input : HorizontalOccurrenceColoredRouteInput) :
    List AxisDirection :=
  unitSubdivisionDirections
    (horizontalOccurrenceClauseCoordinatedRouteComputed input)

/-- Translating the variable fan to its source macrocell does not change its
finite direction word. -/
theorem unitSubdivisionDirections_horizontalOccurrenceVariableStubComputed
    (input : HorizontalOccurrenceColoredRouteInput) :
    unitSubdivisionDirections
        (horizontalOccurrenceVariableStubComputed input) =
      horizontalOccurrenceVariableStubDirections input := by
  simpa only [horizontalOccurrenceVariableStubComputed,
    horizontalOccurrenceVariableStubDirections] using
    unitSubdivisionDirections_translatePolyline
      (PeriodicPlanarOneInThreeToThreeDM.ribbonMacrocellOrigin
        (horizontalPaddedRoutedPositionComputed input.1.1.1 input.1.1.2))
      (horizontalOccurrenceVariableCoordinatedRouteComputed input)

/-- Translating the clause fan to its lifted target macrocell does not change
its finite direction word. -/
theorem unitSubdivisionDirections_horizontalOccurrenceClauseStubComputed
    (input : HorizontalOccurrenceColoredRouteInput) :
    unitSubdivisionDirections
        (horizontalOccurrenceClauseStubComputed input) =
      horizontalOccurrenceClauseStubDirections input := by
  simpa only [horizontalOccurrenceClauseStubComputed,
    horizontalOccurrenceClauseStubDirections] using
    unitSubdivisionDirections_translatePolyline
      (PeriodicPlanarOneInThreeToThreeDM.ribbonMacrocellOrigin
        (horizontalOccurrenceClauseCenterComputed input.1))
      (horizontalOccurrenceClauseCoordinatedRouteComputed input)

end PeriodicCNFStripReduction
end LeanTrominoes

end
