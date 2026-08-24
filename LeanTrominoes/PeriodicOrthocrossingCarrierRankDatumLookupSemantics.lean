/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedLastRepresentativeSelfLookupSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumLookupData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierIdentityCandidateSupport

/-! # Semantics of rank-datum field lookup -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankDatumLookup

open PaddedSupportedLastRepresentativeEqualityRows

/-- If the compact rows equal the aligned identity selector, lookup returns
the requested field once per distinct active identity. -/
theorem selectedFieldValuesAtPeriod_eq_dedupIdentities_map
    (period : Nat) (descriptors : List RouteDescriptor)
    (field : CarrierNodeRankDatum → Nat)
    (rowsEq : paddedCarrierSourceKeyRepresentativeRows descriptors =
      selectedRows
        (paddedCarrierIdentityCandidateStreamAtPeriod period descriptors)) :
    selectedFieldValuesAtPeriod period descriptors field =
      ((paddedCarrierIdentityCandidateStreamAtPeriod
        period descriptors).filterMap Candidate.value).dedup.map fun code =>
          field (carrierNodeRankDatumAtPeriod period code.node) := by
  unfold selectedFieldValuesAtPeriod fieldValuesWithSentinelAtPeriod
  rw [rowsEq]
  exact lookups_selectedRows_selfSupported_map_append_value
    (paddedCarrierIdentityCandidateStreamAtPeriod period descriptors)
    (paddedCarrierIdentityCandidateStream_supported_eq_isSome
      period descriptors)
    (fieldValueAtPeriod period field) 0

end CarrierRankDatumLookup
end LeanTrominoes.PeriodicOrthocrossing
