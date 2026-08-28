/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordFixedFieldRowExpansionSemantics
import LeanTrominoes.LastTrueUnaryValueLookupValidity
import LeanTrominoes.PaddedSupportedCandidateRepresentativeRowLength
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRepresentativeFieldLookupData

/-! # Validity of representative carrier source-key field lookups -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSourceKeyRepresentativeFieldLookup

@[simp] theorem allKeyFields_length
    (key : Option CarrierKeyWords.CarrierKey) :
    (CarrierKeyAllFieldProjector.keyFields key).length = 6 := by
  cases key <;> simp [CarrierKeyAllFieldProjector.keyFields]

theorem componentKeys_length (descriptors : List RouteDescriptor) :
    (CarrierSourceKeyAllFieldStream.componentKeys descriptors).length =
      2 * (paddedCarrierNodeCandidateStream descriptors).length := by
  unfold CarrierSourceKeyAllFieldStream.componentKeys
    CarrierSourceKeyAllFieldStream.componentKeysOfCandidates
    PaddedSupportedLastRepresentativeEqualityRows.values
  induction paddedCarrierNodeCandidateStream descriptors with
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

theorem sourceKeyCandidates_length (descriptors : List RouteDescriptor) :
    (paddedCarrierSourceKeyCandidateStream descriptors).length =
      (paddedCarrierNodeCandidateStream descriptors).length := by
  simp [paddedCarrierSourceKeyCandidateStream]

/-- The candidate-major table, including its sentinel block, has exactly
the width of every expanded representative row. -/
theorem alignedFieldValues_length (descriptors : List RouteDescriptor) :
    (alignedFieldValues descriptors).length =
      (paddedCarrierSourceKeyCandidateStream descriptors).length.succ *
        fieldCount := by
  unfold alignedFieldValues
    CarrierSourceKeyAllFieldStream.fieldValuesWithSentinel fieldCount
  rw [allFieldValuesWithSentinel_length, componentKeys_length,
    sourceKeyCandidates_length]
  omega

theorem expandedRows_forall_length (descriptors : List RouteDescriptor) :
    (expandedRows descriptors).words.Forall fun row =>
      row.length = (alignedFieldValues descriptors).length := by
  unfold expandedRows
  have sourceLengths :=
    PaddedSupportedCandidateWords.representativeRows_forall_length
      CarrierNodeSourceKeys.word
      (paddedCarrierSourceKeyCandidateStream descriptors)
  have expanded :=
    DelimitedBinaryWordFixedFieldRowExpansion.rows_forall_length
      fieldCount
      ((paddedCarrierSourceKeyCandidateStream descriptors).length + 1)
      (paddedCarrierSourceKeyRepresentativeRows descriptors)
      sourceLengths
  rw [alignedFieldValues_length]
  simpa [Nat.succ_eq_add_one] using expanded

def input (descriptors : List RouteDescriptor) :
    LastTrueUnaryValueLookupMachine.Input where
  rows := (expandedRows descriptors).words
  values := alignedFieldValues descriptors
  valid := LastTrueUnaryValueLookupMachine.RowsValid.of_forall_length
    (expandedRows_forall_length descriptors)

end CarrierSourceKeyRepresentativeFieldLookup
end LeanTrominoes.PeriodicOrthocrossing
