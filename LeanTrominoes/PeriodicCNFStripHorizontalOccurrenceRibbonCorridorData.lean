/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseCoordinatedRouteData
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceUnitRouteData
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonCorridorComputation

/-! # Executable central occurrence ribbon corridors -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- Central macrocell corridor on the occurrence's computed physical lane. -/
def horizontalOccurrenceRibbonCorridorCoreComputed
    (input : HorizontalOccurrenceColoredRouteInput) : List Cell :=
  ribbonCorridorCore
    (horizontalOccurrenceRibbonLaneComputed input)
    (horizontalOccurrenceUnitSourceRouteComputed input.1)

end PeriodicCNFStripReduction
end LeanTrominoes
