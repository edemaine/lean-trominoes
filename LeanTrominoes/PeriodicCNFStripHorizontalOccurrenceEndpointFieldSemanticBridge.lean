/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceDirectionRequestSemanticBridge

/-! # Endpoint-field bridge for compact horizontal occurrence requests -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PeriodicPlanarOneInThreeToThreeDM PlanarThreeDM

/-- Matching the decoded variable fan and site slot identifies the complete
finite variable endpoint word. -/
theorem horizontalOccurrenceVariableEndpointFields_direction
    (input : HorizontalOccurrenceColoredRouteInput)
    (variableFan : VariableRibbonFanData)
    (variableSlot : VariableSiteSlot)
    (variableFanEq : variableFan =
      (horizontalOccurrenceVariableCoordinatedRouteInputComputed input).1)
    (variableSlotEq : variableSlot =
      (horizontalOccurrenceVariableCoordinatedRouteInputComputed input).2.1) :
    HorizontalFiniteIncidenceDirectionQuery.directions
        (.variableStub variableFan variableSlot input.2) =
      horizontalOccurrenceVariableStubDirections input := by
  rw [variableFanEq, variableSlotEq]
  exact
    HorizontalFiniteIncidenceDirectionQuery.directions_variableStub_input
      input

/-- A decoded variable endpoint, selected lane, and clause endpoint identify
the complete computed horizontal coordinated word.  The clause endpoint is
kept as a direction equality so clients need not unfold its large source
decoder merely to expose the three finite query fields. -/
theorem horizontalOccurrenceEndpointFields_eq_coordinatedDirections
    (input : HorizontalOccurrenceColoredRouteInput)
    (block : HorizontalRoutedRouteDirectionBlock)
    (variableFan : VariableRibbonFanData)
    (variableSlot : VariableSiteSlot)
    (clauseFan : ClauseRibbonFanData)
    (clauseGroup : X3CClauseTerminalGroup)
    (variableFanEq : variableFan =
      (horizontalOccurrenceVariableCoordinatedRouteInputComputed input).1)
    (variableSlotEq : variableSlot =
      (horizontalOccurrenceVariableCoordinatedRouteInputComputed input).2.1)
    (laneEq : clauseRibbonLaneForColor clauseGroup input.2 =
      horizontalOccurrenceRibbonLaneComputed input)
    (clauseDirectionsEq :
      HorizontalFiniteIncidenceDirectionQuery.directions
          (.clauseStub clauseFan clauseGroup
            (clauseRibbonLaneForColor clauseGroup input.2)) =
        horizontalOccurrenceClauseStubDirections input) :
    HorizontalOccurrenceDirectionRequest.requestedOutput
        (.variableStub variableFan variableSlot input.2)
        (clauseRibbonLaneForColor clauseGroup input.2)
        (horizontalOccurrenceSourceDirections block)
        (.clauseStub clauseFan clauseGroup
          (clauseRibbonLaneForColor clauseGroup input.2)) =
      horizontalOccurrenceCoordinatedDirections input block := by
  exact horizontalOccurrenceDirectionRequest_eq_coordinatedDirections
    input block variableFan variableSlot clauseFan clauseGroup
    (horizontalOccurrenceVariableEndpointFields_direction input
      variableFan variableSlot variableFanEq variableSlotEq)
    laneEq clauseDirectionsEq

end LeanTrominoes.PeriodicCNFStripReduction

end
