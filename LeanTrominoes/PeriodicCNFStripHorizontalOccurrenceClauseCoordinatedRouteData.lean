/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseFanData
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableCoordinatedRouteData

/-! # Executable clause-side coordinated occurrence routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open Gadget PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- Repackage one occurrence as a proof-erased clause-fan entry query.  The
clause-orbit field is irrelevant to the entry lookup and uses zero here. -/
def horizontalOccurrenceClauseFanEntryInputComputed
    (input : HorizontalOccurrenceRouteInput) :
    HorizontalClauseRibbonFanInput × HorizontalClauseOccurrenceEntry :=
  ((input.1.1, 0), (input.1.2, input.2))

/-- Normalized clause-orbit index stored at one occurrence. -/
def horizontalOccurrenceClauseIndexComputed
    (input : HorizontalOccurrenceRouteInput) : Nat :=
  horizontalOccurrenceClauseEntryClauseIndexComputed
    (horizontalOccurrenceClauseFanEntryInputComputed input)

/-- Clause terminal group stored at one occurrence. -/
def horizontalOccurrenceClauseTerminalGroupComputed
    (input : HorizontalOccurrenceRouteInput) : X3CClauseTerminalGroup :=
  horizontalOccurrenceClauseEntryGroupComputed
    (horizontalOccurrenceClauseFanEntryInputComputed input)

/-- Finite group/color query selecting one physical ribbon lane. -/
def horizontalOccurrenceRibbonLaneInputComputed
    (input : HorizontalOccurrenceColoredRouteInput) :
    X3CClauseTerminalGroup × WireColor :=
  (horizontalOccurrenceClauseTerminalGroupComputed input.1, input.2)

/-- Physical ribbon lane selected by an occurrence and semantic color. -/
def horizontalOccurrenceRibbonLaneComputed
    (input : HorizontalOccurrenceColoredRouteInput) : WireColor :=
  clauseRibbonLaneForColor
    (horizontalOccurrenceRibbonLaneInputComputed input).1
    (horizontalOccurrenceRibbonLaneInputComputed input).2

/-- Concrete source and computed clause orbit selecting the finite fan. -/
def horizontalOccurrenceClauseRibbonFanQueryComputed
    (input : HorizontalOccurrenceColoredRouteInput) :
    HorizontalClauseRibbonFanInput :=
  (input.1.1.1, horizontalOccurrenceClauseIndexComputed input.1)

/-- Finite-table input for the clause-side coordinated fan route. -/
def horizontalOccurrenceClauseCoordinatedRouteInputComputed
    (input : HorizontalOccurrenceColoredRouteInput) :
    ClauseRibbonFanData × (X3CClauseTerminalGroup × WireColor) :=
  (horizontalOccurrenceClauseRibbonFanDataComputed
      (horizontalOccurrenceClauseRibbonFanQueryComputed input),
    (horizontalOccurrenceClauseTerminalGroupComputed input.1,
      horizontalOccurrenceRibbonLaneComputed input))

/-- Standard-macrocell clause-side coordinated route for one colored
occurrence. -/
def horizontalOccurrenceClauseCoordinatedRouteComputed
    (input : HorizontalOccurrenceColoredRouteInput) : List Cell :=
  let tableInput :=
    horizontalOccurrenceClauseCoordinatedRouteInputComputed input
  tableInput.1.coordinatedRoute tableInput.2.1 tableInput.2.2

end PeriodicCNFStripReduction
end LeanTrominoes
