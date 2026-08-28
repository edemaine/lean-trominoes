/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierIdentityCandidateStreamMapSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeNormalizedSourceKeySemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedSourceKeyRepresentativeFieldLookupData
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRepresentativeFieldLookupSemantics

/-! # Alignment of normalized carrier representative fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierNormalizedSourceKeyRepresentativeFieldLookup

open PaddedSupportedLastRepresentativeEqualityRows

/-- Twelve normalized source-pair fields reconstructed from one optional
reversible carrier identity. -/
def identityFieldsAtPeriod (period : Nat) :
    Option CarrierNodeCode → List Nat
  | none => CarrierSourceKeyRepresentativeFieldLookup.sourcePairFields none
  | some identity =>
      CarrierSourceKeyRepresentativeFieldLookup.sourcePairFields
        (some (CarrierNodeNormalizedSourceKeys.pairAtPeriod
          period identity.node))

@[simp] theorem identityFieldsAtPeriod_length
    (period : Nat) (identity : Option CarrierNodeCode) :
    (identityFieldsAtPeriod period identity).length =
      CarrierSourceKeyRepresentativeFieldLookup.fieldCount := by
  cases identity <;>
    simp [identityFieldsAtPeriod,
      CarrierSourceKeyRepresentativeFieldLookup.sourcePairFields_length]

private theorem identityCandidateFieldBlocks
    (period : Nat) (candidates : List (Candidate CarrierNode)) :
    ((CarrierNormalizedSourceKeyAllFieldStream.componentKeysOfCandidatesAtPeriod
        period candidates).flatMap
          CarrierKeyAllFieldProjector.keyFields) =
      (values (candidates.map
        (Candidate.mapActiveValue CarrierNode.code))).flatMap
          (identityFieldsAtPeriod period) := by
  unfold CarrierNormalizedSourceKeyAllFieldStream.componentKeysOfCandidatesAtPeriod
    values
  induction candidates with
  | nil => rfl
  | cons candidate candidates induction =>
      rcases candidate with ⟨value, supported⟩
      cases value <;>
        simp [Candidate.mapActiveValue, identityFieldsAtPeriod,
          CarrierSourceKeyRepresentativeFieldLookup.sourcePairFields,
          CarrierSourceKeyRepresentativeFieldLookup.fieldCount,
          CarrierKeyAllFieldProjector.keyFields, induction]

/-- The normalized candidate-major field table is aligned with the existing
reversible identity candidate stream, followed by its rejection sentinel. -/
theorem alignedFieldValuesAtPeriod_eq_identityCandidateFields
    (period : Nat) (descriptors : List RouteDescriptor) :
    alignedFieldValuesAtPeriod period descriptors =
      ((values (paddedCarrierIdentityCandidateStreamAtPeriod
        period descriptors) ++ [none]).flatMap
          (identityFieldsAtPeriod period)) := by
  unfold alignedFieldValuesAtPeriod
    CarrierNormalizedSourceKeyAllFieldStream.fieldValuesWithSentinelAtPeriod
    CarrierNormalizedSourceKeyAllFieldStream.componentKeysAtPeriod
    CarrierKeyAllFieldProjector.valuesWithSentinel
  rw [paddedCarrierIdentityCandidateStreamAtPeriod_eq_mapActiveValue,
    identityCandidateFieldBlocks]
  simp [identityFieldsAtPeriod,
    CarrierSourceKeyRepresentativeFieldLookup.sourcePairFields,
    CarrierSourceKeyRepresentativeFieldLookup.fieldCount]

end CarrierNormalizedSourceKeyRepresentativeFieldLookup
end LeanTrominoes.PeriodicOrthocrossing
