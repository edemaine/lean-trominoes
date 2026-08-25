/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateActiveValueMapSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingRecordSourceFieldNodeStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingRecordSourceFieldRankSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierIdentityCandidateStreamMapSemantics

/-! # Alignment of source-key crossing fields with carrier rank data -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierCrossingRecordSourceField

open PaddedSupportedLastRepresentativeEqualityRows

theorem alignedValuesWithSentinel_eq_fieldValuesWithSentinelAtPeriod
    (field : Field) (period : Nat)
    (descriptors : List RouteDescriptor) :
    alignedValuesWithSentinel field descriptors =
      CarrierRankDatumLookup.fieldValuesWithSentinelAtPeriod
        period descriptors (rankValue field) := by
  unfold alignedValuesWithSentinel
    CarrierRankDatumLookup.fieldValuesWithSentinelAtPeriod
  rw [componentValuesWithSentinel_eq_optionalNodeValues]
  rw [paddedCarrierIdentityCandidateStreamAtPeriod_eq_mapActiveValue]
  rw [values_map_mapActiveValue]
  simp [List.map_map]

end CarrierCrossingRecordSourceField
end LeanTrominoes.PeriodicOrthocrossing

end
