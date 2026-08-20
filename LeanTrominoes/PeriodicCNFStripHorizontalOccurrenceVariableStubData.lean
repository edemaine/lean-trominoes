/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableCoordinatedRouteData
import LeanTrominoes.PeriodicCNFStripHorizontalPaddedRoutedPlacementPositionComputability

/-! # Executable translated variable occurrence stubs -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PeriodicOrthocrossing

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- Coordinated variable fan translated to its executable source macrocell. -/
def horizontalOccurrenceVariableStubComputed
    (input : HorizontalOccurrenceColoredRouteInput) : List Cell :=
  translatePolyline
    (ribbonMacrocellOrigin
      (horizontalPaddedRoutedPositionComputed input.1.1.1 input.1.1.2))
    (horizontalOccurrenceVariableCoordinatedRouteComputed input)

end PeriodicCNFStripReduction
end LeanTrominoes
