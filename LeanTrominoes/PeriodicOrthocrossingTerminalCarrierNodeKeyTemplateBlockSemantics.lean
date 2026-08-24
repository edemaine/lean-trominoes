/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingTerminalCarrierNodeKeyTemplateSemantics

/-! # Carrier-key projection of terminal node template blocks -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PaddedSupportedCandidateBlocks

@[simp] theorem Segment.map_carrierKey_terminalCarrierNodeTemplateBlocks
    (pair : RouteDescriptor × RouteDescriptor)
    (segmentIndex : Nat) (segment : Segment) :
    (segment.terminalCarrierNodeTemplateBlocks
      pair segmentIndex).map
        (List.map (Template.mapValue CarrierNode.carrierKey)) =
      segment.terminalCarrierKeyTemplateBlocks pair segmentIndex := by
  simp [Segment.terminalCarrierNodeTemplateBlocks,
    Segment.terminalCarrierKeyTemplateBlocks]

@[simp] theorem RouteShape.map_carrierKey_terminalCarrierNodeTemplateBlocks
    (shape : RouteShape) (pair : RouteDescriptor × RouteDescriptor) :
    (shape.terminalCarrierNodeTemplateBlocks pair).map
        (List.map (Template.mapValue CarrierNode.carrierKey)) =
      shape.terminalCarrierKeyTemplateBlocks pair := by
  unfold RouteShape.terminalCarrierNodeTemplateBlocks
    RouteShape.terminalCarrierKeyTemplateBlocks
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro tagged _taggedMember
  exact Segment.map_carrierKey_terminalCarrierNodeTemplateBlocks
    pair tagged.2 tagged.1

@[simp] theorem map_carrierKey_terminalCarrierNodeTemplateBlocks
    (pair : RouteDescriptor × RouteDescriptor) :
    (terminalCarrierNodeTemplateBlocks pair).map
        (List.map (Template.mapValue CarrierNode.carrierKey)) =
      terminalCarrierKeyTemplateBlocks pair := by
  unfold terminalCarrierNodeTemplateBlocks
    terminalCarrierKeyTemplateBlocks
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro shape _shapeMember
  exact shape.map_carrierKey_terminalCarrierNodeTemplateBlocks pair

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
