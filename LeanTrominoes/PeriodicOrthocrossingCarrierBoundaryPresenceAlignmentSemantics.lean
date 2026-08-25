/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateActiveValueMapSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPresenceFieldData
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPresenceNodeStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPresenceRankValueSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierIdentityCandidateStreamMapSemantics

/-! # Alignment of carrier boundary presence with rank data -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierBoundaryPresenceField

open PaddedSupportedLastRepresentativeEqualityRows

/-- The sentinel-completed physical-node presence stream is exactly the
aligned boundary-presence field of the padded carrier rank-data identities. -/
theorem alignedValuesWithSentinel_eq_fieldValuesWithSentinelAtPeriod
    (period : Nat) (descriptors : List RouteDescriptor) :
    alignedValuesWithSentinel descriptors =
      CarrierRankDatumLookup.fieldValuesWithSentinelAtPeriod
        period descriptors rankValue := by
  unfold alignedValuesWithSentinel terminalKeys crossingKeys
    CarrierRankDatumLookup.fieldValuesWithSentinelAtPeriod
  rw [componentValuesWithSentinel_eq_optionalNodeValues]
  rw [paddedCarrierIdentityCandidateStreamAtPeriod_eq_mapActiveValue]
  rw [values_map_mapActiveValue]
  simp [List.map_map]

end CarrierBoundaryPresenceField
end LeanTrominoes.PeriodicOrthocrossing

end
