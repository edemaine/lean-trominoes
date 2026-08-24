/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeyWordRecipeData

/-! # Length alignment of terminal carrier-key recipes -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

/-- One route shape has one terminal recipe block for every carrier-segment
classification predicate. -/
@[simp] theorem RouteShape.terminalCarrierKeyRecipeBlocks_length
    (shape : RouteShape) :
    shape.terminalCarrierKeyRecipeBlocks.length =
      shape.carrierSegmentPredicates.length := by
  unfold RouteShape.terminalCarrierKeyRecipeBlocks
    RouteShape.carrierSegmentPredicates
  simp [Segment.terminalCarrierKeyRecipeBlocks,
    Segment.carrierAxisPredicates]

/-- The complete fixed terminal recipe family is length-aligned with the
complete carrier-segment predicate family. -/
@[simp] theorem terminalCarrierKeyRecipeBlocks_length :
    terminalCarrierKeyRecipeBlocks.length =
      carrierSegmentPredicates.length := by
  unfold terminalCarrierKeyRecipeBlocks carrierSegmentPredicates
  simp

/-- Hence every terminal activation word has exactly the number of entries
expected by the recipe family. -/
@[simp] theorem terminalCarrierKeyActivations_length
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    (terminalCarrierKeyActivations tokens).length =
      terminalCarrierKeyRecipeBlocks.length := by
  unfold terminalCarrierKeyActivations
  rw [List.length_map, terminalCarrierKeyRecipeBlocks_length]

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
