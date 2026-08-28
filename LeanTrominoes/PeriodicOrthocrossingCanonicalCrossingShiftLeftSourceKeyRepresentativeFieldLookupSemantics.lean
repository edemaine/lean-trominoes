/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedLastRepresentativeFixedFieldLookupSemantics
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftLeftSourceKeyRepresentativeFieldLookupCompiler
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftLeftSourceKeyRepresentativeSemantics

/-! # Semantics of representative canonical crossing source-pair fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CanonicalCrossingShiftLeftSourceKeyRepresentativeFieldLookup

open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorOccurrenceSlotBinaryWords

@[simp] theorem sourcePairFields_length
    (sourcePair : Option CarrierNodeSourceKeys.SourceKeyPair) :
    (sourcePairFields sourcePair).length = fieldCount := by
  cases sourcePair <;>
    simp [sourcePairFields, fieldCount,
      CarrierKeyAllFieldProjector.keyFields]

private theorem candidateList_eq_carrierNodeCandidates
    (descriptors : List RouteDescriptor) :
    CanonicalCrossingShiftLeftSourceKeyRepresentatives.candidateList descriptors =
      (CanonicalCrossingShiftLeftSourceKeyComponentStream.carrierNodeCandidates
        (taggedDescriptors descriptors ×ˢ
          taggedDescriptors descriptors)).map
            CarrierNodeSourceKeyCandidateWords.sourceKeyCandidate := by
  unfold CanonicalCrossingShiftLeftSourceKeyRepresentatives.candidateList
    CanonicalCrossingShiftLeftSourceKeyStream.candidates
    CanonicalCrossingShiftLeftSourceKeyComponentStream.carrierNodeCandidates
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro pair _pairMember
  rfl

private theorem nodeCandidateFieldBlocks
    (candidates : List (Candidate CarrierNode)) :
    (((values candidates).flatMap fun node =>
          [node.map
              (CanonicalCrossingShiftLeftSourceKeyComponentStream.sourceKey
                .first),
            node.map
              (CanonicalCrossingShiftLeftSourceKeyComponentStream.sourceKey
                .second)]).flatMap CarrierKeyAllFieldProjector.keyFields) =
      ((candidates.map
        CarrierNodeSourceKeyCandidateWords.sourceKeyCandidate).map
          Candidate.value).flatMap sourcePairFields := by
  induction candidates with
  | nil => rfl
  | cons candidate candidates induction =>
      rcases candidate with ⟨value, supported⟩
      have tail := induction
      simp only [PaddedSupportedLastRepresentativeEqualityRows.values] at tail
      cases value <;>
        simp [PaddedSupportedLastRepresentativeEqualityRows.values,
          CarrierNodeSourceKeyCandidateWords.sourceKeyCandidate,
          CanonicalCrossingShiftLeftSourceKeyComponentStream.sourceKey,
          sourcePairFields, CarrierKeyAllFieldProjector.keyFields,
          tail, Function.comp_def]

private theorem nodeCandidateFields
    (candidates : List (Candidate CarrierNode)) :
    CarrierKeyAllFieldProjector.valuesWithSentinel
        ((values candidates).flatMap fun node =>
          [node.map
              (CanonicalCrossingShiftLeftSourceKeyComponentStream.sourceKey
                .first),
            node.map
              (CanonicalCrossingShiftLeftSourceKeyComponentStream.sourceKey
                .second)]) =
      (((candidates.map
          CarrierNodeSourceKeyCandidateWords.sourceKeyCandidate).map
            Candidate.value) ++ [none]).flatMap sourcePairFields := by
  unfold CarrierKeyAllFieldProjector.valuesWithSentinel
  rw [nodeCandidateFieldBlocks, List.flatMap_append]
  simp [sourcePairFields, CarrierKeyAllFieldProjector.keyFields]

/-- The physical candidate-major table is the optional compact source-pair
field block at every representative candidate, followed by `none` as the
rejection sentinel. -/
theorem alignedFieldValues_eq_candidateFields
    (descriptors : List RouteDescriptor) :
    alignedFieldValues descriptors =
      ((CanonicalCrossingShiftLeftSourceKeyRepresentatives.candidateList
        descriptors).map Candidate.value ++ [none]).flatMap
          sourcePairFields := by
  unfold alignedFieldValues
    CanonicalCrossingShiftLeftSourceKeyAllFieldStream.fieldValuesWithSentinel
    CanonicalCrossingShiftLeftSourceKeyAllFieldStream.componentKeys
  rw [candidateList_eq_carrierNodeCandidates]
  exact nodeCandidateFields
    (CanonicalCrossingShiftLeftSourceKeyComponentStream.carrierNodeCandidates
      (taggedDescriptors descriptors ×ˢ
        taggedDescriptors descriptors))

/-- The compiled lookup selects the complete twelve-field block of every
stable compact source pair, in exact representative order. -/
theorem selectedFields_eq_semanticFields
    (descriptors : List RouteDescriptor) :
    selectedFields descriptors = semanticFields descriptors := by
  unfold selectedFields expandedRows semanticFields
  rw [CanonicalCrossingShiftLeftSourceKeyRepresentatives.representativeRows_eq_selectedRows]
  rw [alignedFieldValues_eq_candidateFields]
  exact
    PaddedSupportedLastRepresentativeEqualityRows.lookups_fixedFieldRows_selfSupported
      (CanonicalCrossingShiftLeftSourceKeyRepresentatives.candidateList
        descriptors)
      (CanonicalCrossingShiftLeftSourceKeyRepresentatives.candidateList_supported_eq_isSome
        descriptors)
      sourcePairFields fieldCount sourcePairFields_length

/-- On a valid numeric descriptor presentation, the selected field stream is
the twelve-field image of the canonicalized crossing halo in exact order. -/
theorem selectedFields_eq_canonicalizedCrossingFields
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    (descriptors : List RouteDescriptor)
    (selfIndexed : RouteDescriptorList.SelfIndexed descriptors)
    (commonPeriod :
      ∀ descriptor ∈ descriptors,
        descriptor.gridSize = drawingGridSize graph)
    (localShapes :
      ∀ descriptor ∈ descriptors,
        RouteDescriptorPairAffine.RouteDescriptor.HasLocalShape descriptor)
    (occurrencesEq :
      routeDescriptorNeighborOccurrences descriptors =
        neighborOccurrences graph) :
    selectedFields descriptors =
      ((occurrencePairCanonicalizedCrossingHaloAtPeriod
        (drawingGridSize graph)
        (routeDescriptorNeighborOccurrences descriptors)).map
          RetainedCompactAtomWords.crossingPair).flatMap
            fun sourcePair => sourcePairFields (some sourcePair) := by
  rw [selectedFields_eq_semanticFields]
  unfold semanticFields
  rw [CanonicalCrossingShiftLeftSourceKeyRepresentatives.values_eq_canonicalizedCrossingPairs
    wellFormed degree isLocal descriptors selfIndexed commonPeriod
    localShapes occurrencesEq]

end CanonicalCrossingShiftLeftSourceKeyRepresentativeFieldLookup
end LeanTrominoes.PeriodicOrthocrossing
