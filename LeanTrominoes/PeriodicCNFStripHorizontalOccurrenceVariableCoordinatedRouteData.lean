/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanData

/-! # Executable variable-side coordinated occurrence routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open Gadget
open PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- One normalized occurrence query paired with a ribbon color. -/
abbrev HorizontalOccurrenceColoredRouteInput :=
  HorizontalOccurrenceRouteInput × WireColor

/-- Finite-table input for the variable-side coordinated fan route. -/
def horizontalOccurrenceVariableCoordinatedRouteInputComputed
    (input : HorizontalOccurrenceColoredRouteInput) :
    VariableRibbonFanData × (VariableSiteSlot × WireColor) :=
  (horizontalOccurrenceVariableRibbonFanDataComputed input.1.1,
    (occurrenceVariableSiteSlot input.1.2, input.2))

/-- Standard-macrocell variable-side coordinated route for one colored
occurrence. -/
def horizontalOccurrenceVariableCoordinatedRouteComputed
    (input : HorizontalOccurrenceColoredRouteInput) : List Cell :=
  let tableInput :=
    horizontalOccurrenceVariableCoordinatedRouteInputComputed input
  tableInput.1.coordinatedRoute tableInput.2.1 tableInput.2.2

end PeriodicCNFStripReduction
end LeanTrominoes
