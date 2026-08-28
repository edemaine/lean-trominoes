/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupValidity
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedSourceKeyRepresentativeFieldLookupData
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRepresentativeFieldLookupInput

/-! # Validity of normalized representative field lookups -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierNormalizedSourceKeyRepresentativeFieldLookup

open PaddedSupportedLastRepresentativeEqualityRows

theorem componentKeysOfCandidatesAtPeriod_length
    (period : Nat) (candidates : List (Candidate CarrierNode)) :
    (CarrierNormalizedSourceKeyAllFieldStream.componentKeysOfCandidatesAtPeriod
      period candidates).length = 2 * candidates.length := by
  unfold CarrierNormalizedSourceKeyAllFieldStream.componentKeysOfCandidatesAtPeriod
    PaddedSupportedLastRepresentativeEqualityRows.values
  induction candidates with
  | nil => rfl
  | cons candidate candidates induction =>
      simp [induction, Nat.mul_succ]

theorem alignedFieldValuesAtPeriod_length
    (period : Nat) (descriptors : List RouteDescriptor) :
    (alignedFieldValuesAtPeriod period descriptors).length =
      (paddedCarrierSourceKeyCandidateStream descriptors).length.succ *
        fieldCount := by
  unfold alignedFieldValuesAtPeriod
    CarrierNormalizedSourceKeyAllFieldStream.fieldValuesWithSentinelAtPeriod
    CarrierNormalizedSourceKeyAllFieldStream.componentKeysAtPeriod
    fieldCount CarrierSourceKeyRepresentativeFieldLookup.fieldCount
  rw [CarrierSourceKeyRepresentativeFieldLookup.allFieldValuesWithSentinel_length,
    componentKeysOfCandidatesAtPeriod_length,
    CarrierSourceKeyRepresentativeFieldLookup.sourceKeyCandidates_length]
  omega

theorem expandedRows_forall_length
    (period : Nat) (descriptors : List RouteDescriptor) :
    (expandedRows descriptors).words.Forall fun row =>
      row.length = (alignedFieldValuesAtPeriod period descriptors).length := by
  have physical :=
    CarrierSourceKeyRepresentativeFieldLookup.expandedRows_forall_length
      descriptors
  apply physical.imp
  intro row rowLength
  rw [rowLength,
    CarrierSourceKeyRepresentativeFieldLookup.alignedFieldValues_length,
    alignedFieldValuesAtPeriod_length]

def inputAtPeriod (period : Nat) (descriptors : List RouteDescriptor) :
    LastTrueUnaryValueLookupMachine.Input where
  rows := (expandedRows descriptors).words
  values := alignedFieldValuesAtPeriod period descriptors
  valid := LastTrueUnaryValueLookupMachine.RowsValid.of_forall_length
    (expandedRows_forall_length period descriptors)

@[simp] theorem encode_inputAtPeriod
    (period : Nat) (descriptors : List RouteDescriptor) :
    LastTrueUnaryValueLookupMachine.encode
        (inputAtPeriod period descriptors) =
      SeparatedProductEncoding.encode
        DelimitedBinaryWords.finEncoding.encode
        UnaryFieldEncoderMachine.unaryFields
        (expandedRows descriptors,
          alignedFieldValuesAtPeriod period descriptors) := by
  rfl

@[simp] theorem lookups_inputAtPeriod
    (period : Nat) (descriptors : List RouteDescriptor) :
    LastTrueUnaryValueLookupMachine.lookups
        (inputAtPeriod period descriptors).rows
        (inputAtPeriod period descriptors).values =
      selectedFieldsAtPeriod period descriptors := by
  rfl

theorem encoded_physical_pair_eq_encode_inputAtPeriod
    (period : Nat) (descriptors : List RouteDescriptor)
    (fields : List UnaryFieldEncoderMachine.Symbol)
    (fieldsEq : fields = UnaryFieldEncoderMachine.unaryFields
      (alignedFieldValuesAtPeriod period descriptors)) :
    SeparatedProductEncoding.encode
        DelimitedBinaryWords.finEncoding.encode id
        (CarrierSourceKeyRepresentativeFieldLookup.expandedRows descriptors,
          fields) =
      LastTrueUnaryValueLookupMachine.encode
        (inputAtPeriod period descriptors) := by
  rw [encode_inputAtPeriod, fieldsEq]
  rfl

end CarrierNormalizedSourceKeyRepresentativeFieldLookup
end LeanTrominoes.PeriodicOrthocrossing
