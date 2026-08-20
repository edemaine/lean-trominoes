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
open Gadget

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- Proof-free lane and unit-route input to the corridor assembler. -/
def horizontalOccurrenceRibbonCorridorInputComputed
    (input : HorizontalOccurrenceColoredRouteInput) :
    WireColor × List Cell :=
  (horizontalOccurrenceRibbonLaneComputed input,
    horizontalOccurrenceUnitSourceRouteComputed input.1)

/-- Central macrocell corridor on the occurrence's computed physical lane. -/
def horizontalOccurrenceRibbonCorridorCoreComputed
    (input : HorizontalOccurrenceColoredRouteInput) : List Cell :=
  ribbonCorridorCore
    (horizontalOccurrenceRibbonCorridorInputComputed input).1
    (horizontalOccurrenceRibbonCorridorInputComputed input).2

end PeriodicCNFStripReduction
end LeanTrominoes
