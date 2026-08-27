/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceCoordinatedRouteDirectionBlock
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceDirectionRequestCompiler

/-! # Horizontal occurrence request semantics -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open HorizontalOccurrenceDirectionRequest

/-- Compact finite/dynamic request corresponding to one classified horizontal
occurrence route. -/
def horizontalOccurrenceDirectionRequestTokens
    (input : HorizontalOccurrenceColoredRouteInput)
    (block : HorizontalRoutedRouteDirectionBlock) :
    List HorizontalOccurrenceDirectionRequest.Token :=
  tokens
    (.variableStub
      (horizontalOccurrenceVariableCoordinatedRouteInputComputed input).1
      (horizontalOccurrenceVariableCoordinatedRouteInputComputed input).2.1
      (horizontalOccurrenceVariableCoordinatedRouteInputComputed input).2.2)
    (horizontalOccurrenceRibbonLaneComputed input)
    (horizontalOccurrenceSourceDirections block)
    (.clauseStub
      (horizontalOccurrenceClauseCoordinatedRouteInputComputed input).1
      (horizontalOccurrenceClauseCoordinatedRouteInputComputed input).2.1
      (horizontalOccurrenceClauseCoordinatedRouteInputComputed input).2.2)

/-- The fixed request machine emits the exact complete coordinated occurrence
direction word selected by the compact routed block. -/
@[simp] theorem output_horizontalOccurrenceDirectionRequestTokens
    (input : HorizontalOccurrenceColoredRouteInput)
    (block : HorizontalRoutedRouteDirectionBlock) :
    output (horizontalOccurrenceDirectionRequestTokens input block) =
      horizontalOccurrenceCoordinatedDirections input block := by
  unfold horizontalOccurrenceDirectionRequestTokens
  rw [output_tokens]
  unfold requestedOutput horizontalOccurrenceCoordinatedDirections
  rw [HorizontalFiniteIncidenceDirectionQuery.directions_variableStub_input,
    HorizontalFiniteIncidenceDirectionQuery.directions_clauseStub_input]
  rfl

end PeriodicCNFStripReduction
end LeanTrominoes

end
