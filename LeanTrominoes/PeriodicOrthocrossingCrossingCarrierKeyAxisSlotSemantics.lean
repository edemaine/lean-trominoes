/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingCarrierKeyAxisInactiveSlotSemantics
import LeanTrominoes.PeriodicOrthocrossingCrossingCarrierKeyAxisOccurrencePairSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingPairSemantics

/-! # Axis semantics of one crossing slot -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open PaddedSupportedCandidateBlocks
open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags
open RouteDescriptorPairAffine
open RouteDescriptorPairCarrierKeyWordRecipes

/-- Every fixed crossing slot agrees with the carrier-key axis datum on a
matched tagged descriptor-slot pair, whether rejected or active. -/
theorem Slot.carrierKeyAxisTemplate
    (descriptors : List RouteDescriptor)
    (selfIndexed : ∀ tagged ∈ descriptors.zipIdx,
      tagged.1.edgeIndex = tagged.2)
    (firstShape secondShape : RouteShape)
    (pair : TaggedDescriptor × TaggedDescriptor)
    (firstMatches : firstShape.Matches pair.1.1)
    (secondMatches : secondShape.Matches pair.2.1)
    (firstDescriptorMember : pair.1.1 ∈ descriptors)
    (secondDescriptorMember : pair.2.1 ∈ descriptors)
    (slot : Slot) (slotMember : slot ∈ crossingSlots) :
    List.Forall₂
      (fun axis template =>
        FixedAxisUnaryFields.value
            (slot.evalTokens (descriptorSlotPairTokens pair)) axis =
          RouteDescriptorCarrierKeyAxisDatum.value descriptors
            (Template.activate
              (slot.evalTokens (descriptorSlotPairTokens pair))
              template).value)
      (slot.carrierKeyRecipeBlock.map fun recipe =>
        decide (recipe.side = .first))
      (slot.carrierKeyTemplateBlock (pair.1.1, pair.2.1)) := by
  cases active : slot.evalTokens (descriptorSlotPairTokens pair) with
  | false =>
      simpa only [active] using
        slot.carrierKeyAxisTemplate_inactive descriptors
          (pair.1.1, pair.2.1)
  | true =>
      have filteredMember : slot ∈ crossingSlots.filter (fun candidate =>
          candidate.evalTokens (descriptorSlotPairTokens pair)) :=
        List.mem_filter.mpr ⟨slotMember, active⟩
      rw [filter_crossingSlots_eq_of_matches
        firstShape secondShape pair firstMatches secondMatches]
        at filteredMember
      have selectedMember : slot ∈ routeShapePairCrossingSlots
          (firstShape, secondShape) :=
        (List.mem_filter.mp filteredMember).1
      have selected := slot.occurrence_members_axes_of_active
        (firstShape, secondShape) pair firstMatches secondMatches
        selectedMember active
      simpa [Slot.carrierKeyRecipeBlock, Slot.carrierKeyTemplateBlock,
        active, Template.activate] using
        occurrencePairCrossingCarrierKeyTemplateBlock_axisDatum_of_axes
          descriptors selfIndexed firstShape secondShape
          (pair.1.1, pair.2.1) firstMatches secondMatches
          firstDescriptorMember secondDescriptorMember slot.occurrences
          selected.1.1 selected.1.2 selected.2.1 selected.2.2

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
