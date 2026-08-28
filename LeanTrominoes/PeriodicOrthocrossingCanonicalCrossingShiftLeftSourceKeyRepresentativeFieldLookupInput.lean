/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordFixedFieldRowExpansionSemantics
import LeanTrominoes.LastTrueUnaryValueLookupValidity
import LeanTrominoes.PaddedSupportedCandidateRepresentativeRowLength
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftLeftSourceKeyRepresentativeFieldLookupData

/-! # Validity of representative source-pair field lookup inputs -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CanonicalCrossingShiftLeftSourceKeyRepresentativeFieldLookup

open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorOccurrenceSlotBinaryWords

@[simp] theorem allKeyFields_length
    (key : Option CarrierKeyWords.CarrierKey) :
    (CarrierKeyAllFieldProjector.keyFields key).length = 6 := by
  cases key <;> simp [CarrierKeyAllFieldProjector.keyFields]

theorem componentKeys_length
    (pairs : List (TaggedDescriptor × TaggedDescriptor)) :
    (CanonicalCrossingShiftLeftSourceKeyAllFieldStream.componentKeys pairs).length =
      2 *
        (CanonicalCrossingShiftLeftSourceKeyComponentStream.carrierNodeCandidates
          pairs).length := by
  unfold CanonicalCrossingShiftLeftSourceKeyAllFieldStream.componentKeys
    PaddedSupportedLastRepresentativeEqualityRows.values
  induction (CanonicalCrossingShiftLeftSourceKeyComponentStream.carrierNodeCandidates
    pairs) with
  | nil => rfl
  | cons candidate candidates induction =>
      simp [induction, Nat.mul_succ]

theorem allFieldValuesWithSentinel_length
    (keys : List (Option CarrierKeyWords.CarrierKey)) :
    (CarrierKeyAllFieldProjector.valuesWithSentinel keys).length =
      6 * keys.length + 12 := by
  unfold CarrierKeyAllFieldProjector.valuesWithSentinel
  induction keys with
  | nil => simp
  | cons key keys induction =>
      rw [List.flatMap_cons, List.append_assoc, List.length_append,
        allKeyFields_length, induction]
      simp only [List.length_cons]
      omega

theorem candidateList_length_eq_carrierNodeCandidates_length
    (descriptors : List RouteDescriptor) :
    (CanonicalCrossingShiftLeftSourceKeyRepresentatives.candidateList
      descriptors).length =
      (CanonicalCrossingShiftLeftSourceKeyComponentStream.carrierNodeCandidates
        (taggedDescriptors descriptors ×ˢ
          taggedDescriptors descriptors)).length := by
  unfold CanonicalCrossingShiftLeftSourceKeyRepresentatives.candidateList
    CanonicalCrossingShiftLeftSourceKeyStream.candidates
    CanonicalCrossingShiftLeftSourceKeyComponentStream.carrierNodeCandidates
  induction (taggedDescriptors descriptors ×ˢ
    taggedDescriptors descriptors) with
  | nil => rfl
  | cons pair pairs induction =>
      simp [RouteDescriptorOccurrenceSlotCrossing.canonicalCrossingShiftLeftSourceKeyCandidates,
        induction]

/-- The candidate-major twelve-field table, including its sentinel block,
has exactly the width of every expanded representative row. -/
theorem alignedFieldValues_length (descriptors : List RouteDescriptor) :
    (alignedFieldValues descriptors).length =
      (CanonicalCrossingShiftLeftSourceKeyRepresentatives.candidateList
          descriptors).length.succ * fieldCount := by
  unfold alignedFieldValues
    CanonicalCrossingShiftLeftSourceKeyAllFieldStream.fieldValuesWithSentinel
    fieldCount
  rw [allFieldValuesWithSentinel_length, componentKeys_length]
  rw [candidateList_length_eq_carrierNodeCandidates_length]
  omega

theorem expandedRows_forall_length (descriptors : List RouteDescriptor) :
    (expandedRows descriptors).words.Forall fun row =>
      row.length = (alignedFieldValues descriptors).length := by
  unfold expandedRows
  have sourceLengths :=
    PaddedSupportedCandidateWords.representativeRows_forall_length
      CarrierNodeSourceKeys.word
      (CanonicalCrossingShiftLeftSourceKeyRepresentatives.candidateList
        descriptors)
  have expanded :=
    DelimitedBinaryWordFixedFieldRowExpansion.rows_forall_length
      fieldCount
      ((CanonicalCrossingShiftLeftSourceKeyRepresentatives.candidateList
        descriptors).length + 1)
      (CanonicalCrossingShiftLeftSourceKeyRepresentatives.representativeRows
        descriptors)
      sourceLengths
  rw [alignedFieldValues_length]
  simpa [Nat.succ_eq_add_one] using expanded

/-- Promised input for the generic last-true unary lookup machine. -/
def input (descriptors : List RouteDescriptor) :
    LastTrueUnaryValueLookupMachine.Input where
  rows := (expandedRows descriptors).words
  values := alignedFieldValues descriptors
  valid := LastTrueUnaryValueLookupMachine.RowsValid.of_forall_length
    (expandedRows_forall_length descriptors)

end CanonicalCrossingShiftLeftSourceKeyRepresentativeFieldLookup
end LeanTrominoes.PeriodicOrthocrossing
