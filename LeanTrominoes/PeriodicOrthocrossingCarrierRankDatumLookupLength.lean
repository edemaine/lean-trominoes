/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumLookupData

/-! # Alignment length of carrier rank-datum field lookup -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankDatumLookup

/-- Every sentinel-completed rank field is aligned with the compact
source-key candidate slots. -/
theorem fieldValuesWithSentinelAtPeriod_length
    (period : Nat) (descriptors : List RouteDescriptor)
    (field : CarrierNodeRankDatum → Nat) :
    (fieldValuesWithSentinelAtPeriod
      period descriptors field).length =
      (paddedCarrierSourceKeyCandidateStream descriptors).length + 1 := by
  unfold fieldValuesWithSentinelAtPeriod
    paddedCarrierIdentityCandidateStreamAtPeriod
    paddedCarrierRankDatumCandidateStreamAtPeriod
    paddedCarrierSourceKeyCandidateStream
    PaddedSupportedLastRepresentativeEqualityRows.values
  simp

end CarrierRankDatumLookup
end LeanTrominoes.PeriodicOrthocrossing
