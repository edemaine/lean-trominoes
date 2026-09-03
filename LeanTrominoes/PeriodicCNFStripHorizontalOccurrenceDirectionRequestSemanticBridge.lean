/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceCoordinatedRouteDirectionBlock
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceDirectionRequestData

/-! # Semantic bridge for compact horizontal occurrence requests -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PeriodicPlanarOneInThreeToThreeDM PlanarThreeDM

/-- Once their finite endpoint fields agree, a compact direct request denotes
exactly the complete horizontal coordinated occurrence direction word. -/
theorem horizontalOccurrenceDirectionRequest_eq_coordinatedDirections
    (input : HorizontalOccurrenceColoredRouteInput)
    (block : HorizontalRoutedRouteDirectionBlock)
    (variableFan : VariableRibbonFanData)
    (variableSlot : VariableSiteSlot)
    (clauseFan : ClauseRibbonFanData)
    (clauseGroup : X3CClauseTerminalGroup)
    (variableDirectionsEq :
      HorizontalFiniteIncidenceDirectionQuery.directions
          (.variableStub variableFan variableSlot input.2) =
        horizontalOccurrenceVariableStubDirections input)
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
  unfold HorizontalOccurrenceDirectionRequest.requestedOutput
  unfold horizontalOccurrenceCoordinatedDirections
  unfold horizontalOccurrenceRibbonCorridorDirections
  rw [variableDirectionsEq, clauseDirectionsEq, laneEq]

end LeanTrominoes.PeriodicCNFStripReduction

end
