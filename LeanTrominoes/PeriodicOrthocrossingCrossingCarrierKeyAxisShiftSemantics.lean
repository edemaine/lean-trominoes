/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierKeyAxisAffineOccurrenceSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingCarrierKeyTemplateData

/-! # Axis semantics of one retained crossing shift -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PaddedSupportedCandidateBlocks
open RouteDescriptorPairFieldTags

/-- One shifted four-template crossing block agrees with the carrier-key axis
datum when its selected occurrence pair is horizontal first and vertical
second. -/
theorem occurrencePairCrossingCarrierKeyShiftTemplateBlock_axisDatum_of_axes
    (descriptors : List RouteDescriptor)
    (selfIndexed : ∀ tagged ∈ descriptors.zipIdx,
      tagged.1.edgeIndex = tagged.2)
    (firstShape secondShape : RouteShape)
    (pair : RouteDescriptor × RouteDescriptor)
    (firstMatches : firstShape.Matches pair.1)
    (secondMatches : secondShape.Matches pair.2)
    (firstDescriptorMember : pair.1 ∈ descriptors)
    (secondDescriptorMember : pair.2 ∈ descriptors)
    (occurrences : Occurrence × Occurrence)
    (firstOccurrenceMember : occurrences.1 ∈
      firstShape.occurrences .first)
    (secondOccurrenceMember : occurrences.2 ∈
      secondShape.occurrences .second)
    (firstHorizontal :
      (occurrences.1.evalPair .first pair).1.segment.IsHorizontal)
    (secondVertical :
      (occurrences.2.evalPair .second pair).1.segment.IsVertical)
    (shift : Cell) :
    List.Forall₂
      (fun axis template =>
        FixedAxisUnaryFields.value true axis =
          RouteDescriptorCarrierKeyAxisDatum.value descriptors
            (some template.value))
      [true, true, false, false]
      (occurrencePairCrossingCarrierKeyShiftTemplateBlock
        pair occurrences shift) := by
  apply occurrencePairCrossingCarrierKeyShiftTemplateBlock_axisDatum
    (FixedAxisUnaryFields.value true)
    (RouteDescriptorCarrierKeyAxisDatum.value descriptors)
  · have datum := occurrences.1.axisDatum_segmentOccurrenceKey
      descriptors selfIndexed firstShape .first pair firstMatches
      firstDescriptorMember firstOccurrenceMember
      (Cell.add occurrences.1.translate shift)
    simpa [Occurrence.carrierKeyAtShift, occurrenceCarrierKey,
      FixedAxisUnaryFields.value, firstHorizontal] using datum.symm
  · have datum := occurrences.2.axisDatum_segmentOccurrenceKey
      descriptors selfIndexed secondShape .second pair secondMatches
      secondDescriptorMember secondOccurrenceMember
      (Cell.add occurrences.2.translate shift)
    have secondNotHorizontal :
        ¬(occurrences.2.evalPair .second pair).1.segment.IsHorizontal := by
      intro secondHorizontal
      exact secondVertical.2 secondHorizontal.1
    simpa [Occurrence.carrierKeyAtShift, occurrenceCarrierKey,
      FixedAxisUnaryFields.value, secondNotHorizontal] using datum.symm

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
