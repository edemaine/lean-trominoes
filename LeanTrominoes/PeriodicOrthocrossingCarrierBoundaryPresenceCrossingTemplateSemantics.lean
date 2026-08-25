/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlockMap
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPresenceRankValueData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingCarrierNodeTemplateData

/-! # Boundary-presence projection of crossing carrier-node templates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PaddedSupportedCandidateBlocks

@[simp] theorem map_boundaryPresence_occurrencePairCrossingCarrierNodeShiftTemplateBlock
    (pair : RouteDescriptor × RouteDescriptor)
    (occurrences : Occurrence × Occurrence) (shift : Cell) :
    (occurrencePairCrossingCarrierNodeShiftTemplateBlock
        pair occurrences shift).map
        (Template.mapValue CarrierBoundaryPresenceField.nodeValue) =
      (occurrencePairCrossingCarrierNodeShiftTemplateBlock
        pair occurrences shift).map
        (Template.mapValue fun _ => 1) := by
  simp [occurrencePairCrossingCarrierNodeShiftTemplateBlock,
    Template.mapValue, CarrierBoundaryPresenceField.nodeValue]

@[simp] theorem map_boundaryPresence_occurrencePairCrossingCarrierNodeTemplateBlock
    (pair : RouteDescriptor × RouteDescriptor)
    (occurrences : Occurrence × Occurrence) :
    (occurrencePairCrossingCarrierNodeTemplateBlock pair occurrences).map
        (Template.mapValue CarrierBoundaryPresenceField.nodeValue) =
      (occurrencePairCrossingCarrierNodeTemplateBlock pair occurrences).map
        (Template.mapValue fun _ => 1) := by
  unfold occurrencePairCrossingCarrierNodeTemplateBlock
  rw [List.map_flatMap, List.map_flatMap]
  apply List.flatMap_congr
  intro shift _shiftMember
  exact
    map_boundaryPresence_occurrencePairCrossingCarrierNodeShiftTemplateBlock
      pair occurrences shift

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
