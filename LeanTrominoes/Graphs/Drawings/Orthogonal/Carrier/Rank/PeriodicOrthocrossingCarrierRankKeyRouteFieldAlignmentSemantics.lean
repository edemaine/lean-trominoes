/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Computation.Compiler.PaddedSupportedCandidateActiveValueMapSemantics
import LeanTrominoes.Graphs.Drawings.Orthogonal.Carrier.Identity.PeriodicOrthocrossingCarrierIdentityCandidateStreamMapSemantics
import LeanTrominoes.Graphs.Drawings.Orthogonal.Carrier.Node.PeriodicOrthocrossingCarrierNodeCodeSemantics
import LeanTrominoes.Graphs.Drawings.Orthogonal.Carrier.Rank.PeriodicOrthocrossingCarrierRankDatumLookupData
import LeanTrominoes.Graphs.Drawings.Orthogonal.Carrier.Rank.PeriodicOrthocrossingCarrierRankKeyRouteFieldData

/-! # Alignment of carrier-key route values with rank data -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeyRouteField

open PaddedSupportedLastRepresentativeEqualityRows

/-- The sentinel-completed route stream is exactly the aligned route-index
field of the padded carrier rank-datum identities at every period. -/
theorem alignedValuesWithSentinel_eq_fieldValuesWithSentinelAtPeriod
    (period : Nat) (descriptors : List RouteDescriptor) :
    alignedValuesWithSentinel descriptors =
      CarrierRankDatumLookup.fieldValuesWithSentinelAtPeriod
        period descriptors (fun datum => datum.key.1) := by
  unfold alignedValuesWithSentinel
    CarrierActiveKeyRecipeStream.semanticKeys
    CarrierRankDatumLookup.fieldValuesWithSentinelAtPeriod
  rw [paddedCarrierIdentityCandidateStreamAtPeriod_eq_mapActiveValue,
    values_map_mapActiveValue]
  simp only [List.map_map]
  apply congrArg (fun fields : List Nat => fields ++ [0])
  apply List.map_congr_left
  intro node _nodeMember
  cases node <;> simp [CarrierKeyRouteFieldProjector.value,
    CarrierRankDatumLookup.fieldValueAtPeriod,
    carrierNodeRankDatumAtPeriod]

end CarrierRankKeyRouteField
end LeanTrominoes.PeriodicOrthocrossing

end
