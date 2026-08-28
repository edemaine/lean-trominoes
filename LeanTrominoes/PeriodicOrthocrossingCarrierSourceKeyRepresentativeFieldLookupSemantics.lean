/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedLastRepresentativeFixedFieldLookupSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRepresentativeFieldLookupCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRepresentativeRowSemantics

/-! # Semantics of representative carrier source-key fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSourceKeyRepresentativeFieldLookup

open PaddedSupportedLastRepresentativeEqualityRows

@[simp] theorem sourcePairFields_length
    (sourcePair : Option CarrierNodeSourceKeys.SourceKeyPair) :
    (sourcePairFields sourcePair).length = fieldCount := by
  cases sourcePair <;>
    simp [sourcePairFields, fieldCount,
      CarrierKeyAllFieldProjector.keyFields]

private theorem nodeCandidateFieldBlocks
    (candidates : List (Candidate CarrierNode)) :
    (((values candidates).flatMap fun node =>
          [node.map fun value => (CarrierNodeSourceKeys.pair value).1,
            node.map fun value =>
              (CarrierNodeSourceKeys.pair value).2]).flatMap
        CarrierKeyAllFieldProjector.keyFields) =
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
          sourcePairFields, fieldCount,
          CarrierKeyAllFieldProjector.keyFields, tail,
          Function.comp_def]

private theorem nodeCandidateFields
    (candidates : List (Candidate CarrierNode)) :
    CarrierKeyAllFieldProjector.valuesWithSentinel
        (CarrierSourceKeyAllFieldStream.componentKeysOfCandidates candidates) =
      (((candidates.map
          CarrierNodeSourceKeyCandidateWords.sourceKeyCandidate).map
            Candidate.value) ++ [none]).flatMap sourcePairFields := by
  unfold CarrierKeyAllFieldProjector.valuesWithSentinel
  unfold CarrierSourceKeyAllFieldStream.componentKeysOfCandidates
  rw [nodeCandidateFieldBlocks, List.flatMap_append]
  simp [sourcePairFields, fieldCount]

/-- The physical candidate-major table is the optional compact source-pair
field block at every candidate, followed by the rejection sentinel. -/
theorem alignedFieldValues_eq_candidateFields
    (descriptors : List RouteDescriptor) :
    alignedFieldValues descriptors =
      ((paddedCarrierSourceKeyCandidateStream descriptors).map
          Candidate.value ++ [none]).flatMap sourcePairFields := by
  unfold alignedFieldValues
    CarrierSourceKeyAllFieldStream.fieldValuesWithSentinel
    CarrierSourceKeyAllFieldStream.componentKeys
    paddedCarrierSourceKeyCandidateStream
  exact nodeCandidateFields (paddedCarrierNodeCandidateStream descriptors)

/-- Lookup selects all twelve fields of every stable compact source-key pair
in exact deduplication order. -/
theorem selectedFields_eq_semanticFields
    (descriptors : List RouteDescriptor) :
    selectedFields descriptors = semanticFields descriptors := by
  unfold selectedFields expandedRows semanticFields
  rw [paddedCarrierSourceKeyRepresentativeRows_eq_selectedRows,
    alignedFieldValues_eq_candidateFields]
  exact
    PaddedSupportedLastRepresentativeEqualityRows.lookups_fixedFieldRows_selfSupported
      (paddedCarrierSourceKeyCandidateStream descriptors)
      (paddedCarrierSourceKeyCandidateStream_supported_eq_isSome descriptors)
      sourcePairFields fieldCount sourcePairFields_length

end CarrierSourceKeyRepresentativeFieldLookup
end LeanTrominoes.PeriodicOrthocrossing
