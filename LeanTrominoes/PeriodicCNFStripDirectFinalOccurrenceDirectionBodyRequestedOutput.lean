/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalColoredOccurrenceDirectionBodyBlockSemantics
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceRoutedRequestCompiler

/-! # Requested-output form of direct occurrence bodies -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PeriodicThreeDM PlanarThreeDM
open PeriodicPlanarOneInThreeToThreeDM

/-- A direct occurrence's three colored bodies have exactly the finite
variable stub, routed corridor, and finite clause stub presentation used by
the horizontal occurrence compiler. -/
theorem directFinalOccurrenceDirectionBodyBlock_eq_requestedOutputs
    (frame : DirectFinalOccurrenceFrame.Data)
    (pair : HorizontalRoutedRouteHeaderTail.Header × List AxisDirection) :
    directFinalOccurrenceDirectionBodyBlock frame pair =
      (incidenceColors.map fun color =>
        let lane :=
          clauseRibbonLaneForColor frame.clauseFrame.group color
        HorizontalOccurrenceDirectionRequest.requestedOutput
          (.variableStub frame.variableFan
            (occurrenceVariableSiteSlot frame.occurrenceSlot) color)
          lane
          (horizontalOccurrenceSourceDirections
            (HorizontalRoutedRouteHeader.block pair.1 pair.2))
          (.clauseStub frame.clauseFrame.clauseFan
            frame.clauseFrame.group lane)) := by
  unfold directFinalOccurrenceDirectionBodyBlock
  apply List.map_congr_left
  intro color _colorMember
  unfold DirectFinalOccurrenceEndpointFrame.routedTokens
  rw [HorizontalOccurrenceRoutedRequest.output_tokens]
  rfl

end LeanTrominoes.PeriodicCNFStripReduction

end
