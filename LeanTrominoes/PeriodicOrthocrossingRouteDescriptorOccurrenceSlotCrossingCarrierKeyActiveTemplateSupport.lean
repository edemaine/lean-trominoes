/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlockMappedSupport
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingPairSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingCarrierKeyTemplateSupport

/-! # Active support of one slot-major crossing template family -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open PaddedSupportedCandidateBlocks
open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags
open RouteDescriptorPairAffine

/-- For two descriptors with selected matching shapes, every active slot in
the fixed crossing scan carries exact global terminal-stream support. -/
theorem crossingCarrierKeyTemplateBlocks_correctActive_of_matches
    (descriptors : List RouteDescriptor)
    (selfIndexed : ∀ tagged ∈ descriptors.zipIdx,
      tagged.1.edgeIndex = tagged.2)
    (firstShape secondShape : RouteShape)
    (pair : TaggedDescriptor × TaggedDescriptor)
    (firstMatches : firstShape.Matches pair.1.1)
    (secondMatches : secondShape.Matches pair.2.1)
    (firstDescriptorMember : pair.1.1 ∈ descriptors)
    (secondDescriptorMember : pair.2.1 ∈ descriptors) :
    CorrectActiveTemplates
      (occurrenceTerminalCarrierKeys
        (routeDescriptorNeighborOccurrences descriptors))
      (crossingActivations (descriptorSlotPairTokens pair))
      (crossingCarrierKeyTemplateBlocks (pair.1.1, pair.2.1)) := by
  unfold crossingActivations crossingCarrierKeyTemplateBlocks
  apply correctActiveTemplates_map
  intro slot slotMember
  cases active : slot.evalTokens (descriptorSlotPairTokens pair) with
  | false => simp
  | true =>
      simp only [if_true]
      have filteredMember : slot ∈ crossingSlots.filter (fun candidate =>
          candidate.evalTokens (descriptorSlotPairTokens pair)) :=
        List.mem_filter.mpr ⟨slotMember, active⟩
      rw [filter_crossingSlots_eq_of_matches
        firstShape secondShape pair firstMatches secondMatches]
        at filteredMember
      have selectedMember : slot ∈ routeShapePairCrossingSlots
          (firstShape, secondShape) :=
        (List.mem_filter.mp filteredMember).1
      unfold routeShapePairCrossingSlots at selectedMember
      rcases List.mem_map.mp selectedMember with
        ⟨taggedOccurrences, taggedOccurrencesMember, slotEq⟩
      subst slot
      have occurrenceMembers :=
        List.mem_product.mp taggedOccurrencesMember
      intro template templateMember
      have templateCorrect :=
        occurrencePairCrossingCarrierKeyTemplateBlock_correct
          descriptors selfIndexed firstShape secondShape
          (pair.1.1, pair.2.1) firstMatches secondMatches
          firstDescriptorMember secondDescriptorMember
          (taggedOccurrences.1.1, taggedOccurrences.2.1)
          (List.fst_mem_of_mem_zipIdx occurrenceMembers.1)
          (List.fst_mem_of_mem_zipIdx occurrenceMembers.2)
          template (by
            simpa [Slot.carrierKeyTemplateBlock] using templateMember)
      exact templateCorrect.trans (by
        by_cases member : template.value ∈
            occurrenceTerminalCarrierKeys
              (routeDescriptorNeighborOccurrences descriptors) <;>
          simp [member])

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
