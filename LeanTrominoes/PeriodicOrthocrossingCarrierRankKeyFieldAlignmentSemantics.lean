/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateActiveValueMapSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierIdentityCandidateStreamMapSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeCodeSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyFieldRankValueData

/-! # Alignment of all carrier-key fields with rank data -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeyField

open PaddedSupportedLastRepresentativeEqualityRows

/-- Every sentinel-completed physical-key column is the corresponding
aligned field of the padded carrier rank-datum identities. -/
theorem alignedValuesWithSentinel_eq_fieldValuesWithSentinelAtPeriod
    (field : CarrierKeyFieldProjector.Field)
    (period : Nat) (descriptors : List RouteDescriptor) :
    alignedValuesWithSentinel field descriptors =
      CarrierRankDatumLookup.fieldValuesWithSentinelAtPeriod
        period descriptors (rankValue field) := by
  unfold alignedValuesWithSentinel
    CarrierActiveKeyRecipeStream.semanticKeys
    CarrierRankDatumLookup.fieldValuesWithSentinelAtPeriod
  rw [paddedCarrierIdentityCandidateStreamAtPeriod_eq_mapActiveValue,
    values_map_mapActiveValue]
  simp only [List.map_map]
  apply congrArg (fun fields : List Nat => fields ++ [0])
  apply List.map_congr_left
  intro node _nodeMember
  cases node with
  | none => rfl
  | some node =>
      cases field <;>
        simp [CarrierKeyFieldProjector.value,
          CarrierKeyFieldProjector.keyValue,
          CarrierRankDatumLookup.fieldValueAtPeriod, rankValue,
          carrierNodeRankDatumAtPeriod]

end CarrierRankKeyField
end LeanTrominoes.PeriodicOrthocrossing

end
