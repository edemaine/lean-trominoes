/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectFinalOccurrenceEndpointFrameData
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceRoutedRequestCompiler
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceCoordinatedRouteDirectionBlock

/-! # Complete framed occurrence requests with actual horizontal endpoints -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction.DirectFinalOccurrenceEndpointFrame

/-- Correct endpoint fields identify the complete direct request with the
existing canonical horizontal semantic request, for any compact block. -/
theorem routedTokens_eq_semanticTokens
    (frame : DirectFinalOccurrenceFrame.Data)
    (input : HorizontalOccurrenceColoredRouteInput)
    (block : HorizontalRoutedRouteDirectionBlock)
    (variableFan : frame.variableFan =
      horizontalOccurrenceVariableRibbonFanDataComputed input.1.1)
    (slot : frame.occurrenceSlot = input.1.2)
    (clauseFan : frame.clauseFrame.clauseFan =
      horizontalOccurrenceClauseRibbonFanDataComputed
        (horizontalOccurrenceClauseRibbonFanQueryComputed input))
    (group : frame.clauseFrame.group =
      horizontalOccurrenceClauseTerminalGroupComputed input.1) :
    routedTokens (ofColor frame input.2) block =
      HorizontalOccurrenceRoutedRequest.semanticTokens input block := by
  simp only [routedTokens, ofColor, variableFan, slot, clauseFan, group,
    HorizontalOccurrenceRoutedRequest.semanticTokens,
    horizontalOccurrenceVariableCoordinatedRouteInputComputed,
    horizontalOccurrenceClauseCoordinatedRouteInputComputed,
    horizontalOccurrenceRibbonLaneComputed,
    horizontalOccurrenceRibbonLaneInputComputed]

/-- The existing interpreter correctness theorem then gives the actual
horizontal coordinated word without reproving its finite-table semantics. -/
theorem output_routedTokens_eq_horizontal
    (frame : DirectFinalOccurrenceFrame.Data)
    (input : HorizontalOccurrenceColoredRouteInput)
    (block : HorizontalRoutedRouteDirectionBlock)
    (variableFan : frame.variableFan =
      horizontalOccurrenceVariableRibbonFanDataComputed input.1.1)
    (slot : frame.occurrenceSlot = input.1.2)
    (clauseFan : frame.clauseFrame.clauseFan =
      horizontalOccurrenceClauseRibbonFanDataComputed
        (horizontalOccurrenceClauseRibbonFanQueryComputed input))
    (group : frame.clauseFrame.group =
      horizontalOccurrenceClauseTerminalGroupComputed input.1) :
    HorizontalOccurrenceRoutedRequest.output
        (routedTokens (ofColor frame input.2) block) =
      horizontalOccurrenceCoordinatedDirections input block := by
  rw [routedTokens_eq_semanticTokens frame input block variableFan slot clauseFan group,
    HorizontalOccurrenceRoutedRequest.output_semanticTokens]

end LeanTrominoes.PeriodicCNFStripReduction.DirectFinalOccurrenceEndpointFrame

end
