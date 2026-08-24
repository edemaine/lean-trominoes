/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FixedAxisUnaryFieldsActiveDatumBlocksMap
import LeanTrominoes.PeriodicOrthocrossingCrossingCarrierKeyAxisSlotSemantics
import LeanTrominoes.PeriodicOrthocrossingCrossingCarrierKeyAxisValueData

/-! # Active datum semantics of the complete crossing-slot scan -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags
open RouteDescriptorPairAffine
open RouteDescriptorPairCarrierKeyWordRecipes

/-- The activation, axis-block, and candidate-template streams of a matched
tagged descriptor-slot pair agree with the carrier-key axis datum. -/
theorem crossingCarrierKeyActiveDatumBlocks_of_matches
    (descriptors : List RouteDescriptor)
    (selfIndexed : ∀ tagged ∈ descriptors.zipIdx,
      tagged.1.edgeIndex = tagged.2)
    (firstShape secondShape : RouteShape)
    (pair : TaggedDescriptor × TaggedDescriptor)
    (firstMatches : firstShape.Matches pair.1.1)
    (secondMatches : secondShape.Matches pair.2.1)
    (firstDescriptorMember : pair.1.1 ∈ descriptors)
    (secondDescriptorMember : pair.2.1 ∈ descriptors) :
    FixedAxisUnaryFields.ActiveDatumBlocks
      (RouteDescriptorCarrierKeyAxisDatum.value descriptors)
      (crossingActivations (descriptorSlotPairTokens pair))
      crossingCarrierKeyRecipeAxisBlocks
      (crossingCarrierKeyTemplateBlocks (pair.1.1, pair.2.1)) := by
  unfold crossingActivations crossingCarrierKeyRecipeAxisBlocks
    crossingCarrierKeyRecipeBlocks crossingCarrierKeyTemplateBlocks
  rw [List.map_map]
  apply FixedAxisUnaryFields.activeDatumBlocks_map
  intro slot slotMember
  exact slot.carrierKeyAxisTemplate descriptors selfIndexed
    firstShape secondShape pair firstMatches secondMatches
    firstDescriptorMember secondDescriptorMember slotMember

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
