/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlockMap
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeyTemplateData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierNodeTemplateData

/-! # Carrier-key projection of one terminal node block -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PaddedSupportedCandidateBlocks

@[simp] theorem Segment.map_carrierKey_terminalCarrierNodeTemplateBlock
    (pair : RouteDescriptor × RouteDescriptor)
    (segmentIndex : Nat) (segment : Segment) :
    (segment.terminalCarrierNodeTemplateBlock
      pair segmentIndex).map
        (Template.mapValue CarrierNode.carrierKey) =
      segment.terminalCarrierKeyTemplateBlock pair segmentIndex := by
  unfold Segment.terminalCarrierNodeTemplateBlock
    Segment.terminalCarrierKeyTemplateBlock
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro translate _translateMember
  simp [Template.mapValue, CarrierNode.carrierKey,
    SegmentTerminal.carrierKey,
    PeriodicGridDrawing.SegmentOccurrenceKey]

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
