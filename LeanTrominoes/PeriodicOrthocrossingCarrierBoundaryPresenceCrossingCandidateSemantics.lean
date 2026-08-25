/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPresenceCrossingTemplateSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierNodeStreamData

/-! # Boundary-presence projection of crossing carrier-node candidates -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open PaddedSupportedCandidateBlocks
open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorPairAffine

@[simp] theorem Slot.map_boundaryPresence_carrierNodeTemplateBlock
    (pair : RouteDescriptor × RouteDescriptor) (slot : Slot) :
    (slot.carrierNodeTemplateBlock pair).map
        (Template.mapValue CarrierBoundaryPresenceField.nodeValue) =
      (slot.carrierNodeTemplateBlock pair).map
        (Template.mapValue fun _ => 1) := by
  unfold Slot.carrierNodeTemplateBlock
  exact
    map_boundaryPresence_occurrencePairCrossingCarrierNodeTemplateBlock
      pair slot.occurrences

@[simp] theorem map_boundaryPresence_crossingCarrierNodeTemplateBlocks
    (pair : RouteDescriptor × RouteDescriptor) :
    (crossingCarrierNodeTemplateBlocks pair).map
        (List.map
          (Template.mapValue CarrierBoundaryPresenceField.nodeValue)) =
      (crossingCarrierNodeTemplateBlocks pair).map
        (List.map (Template.mapValue fun _ => 1)) := by
  simp [crossingCarrierNodeTemplateBlocks]

@[simp] theorem map_boundaryPresence_paddedCrossingCarrierNodeCandidates
    (pair : TaggedDescriptor × TaggedDescriptor) :
    (paddedCrossingCarrierNodeCandidates pair).map
        (Candidate.mapValue CarrierBoundaryPresenceField.nodeValue) =
      (paddedCrossingCarrierNodeCandidates pair).map
        (Candidate.mapValue fun _ => 1) := by
  unfold paddedCrossingCarrierNodeCandidates
  rw [candidates_mapValue, candidates_mapValue]
  rw [map_boundaryPresence_crossingCarrierNodeTemplateBlocks]

@[simp] theorem map_boundaryPresence_paddedCrossingCarrierNodeCandidateStream
    (descriptors : List RouteDescriptor) :
    (paddedCrossingCarrierNodeCandidateStream descriptors).map
        (Candidate.mapValue CarrierBoundaryPresenceField.nodeValue) =
      (paddedCrossingCarrierNodeCandidateStream descriptors).map
        (Candidate.mapValue fun _ => 1) := by
  unfold paddedCrossingCarrierNodeCandidateStream
  rw [List.map_flatMap, List.map_flatMap]
  apply List.flatMap_congr
  intro pair _pairMember
  exact map_boundaryPresence_paddedCrossingCarrierNodeCandidates pair

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing

end
