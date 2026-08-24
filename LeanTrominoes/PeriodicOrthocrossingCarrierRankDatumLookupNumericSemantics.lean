/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumLookupSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyIdentityRepresentativeRowSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierIdentityCandidateNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierRankDatumIdentityDedupSemantics

/-! # Numeric-route rank-datum field lookup semantics -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankDatumLookup

open PaddedSupportedLastRepresentativeEqualityRows

/-- On valid numeric CNF routes, compact representative-row lookup returns
any requested natural field over the exact stably deduplicated rank data. -/
theorem selectedFieldValuesAtPeriod_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ [])
    (field : CarrierNodeRankDatum → Nat) :
    selectedFieldValuesAtPeriod
        (routeDescriptorStreamGridSize
          (PeriodicCNF.numericRouteDescriptors formula))
        (PeriodicCNF.numericRouteDescriptors formula) field =
      (routeDescriptorCarrierRankDatumsAtPeriod
        (routeDescriptorStreamGridSize
          (PeriodicCNF.numericRouteDescriptors formula))
        (PeriodicCNF.numericRouteDescriptors formula)).dedup.map field := by
  let period := routeDescriptorStreamGridSize
    (PeriodicCNF.numericRouteDescriptors formula)
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  have rowsEq :
      paddedCarrierSourceKeyRepresentativeRows descriptors =
        selectedRows
          (paddedCarrierIdentityCandidateStreamAtPeriod
            period descriptors) := by
    rw [paddedCarrierSourceKeyRepresentativeRows_eq_identityRepresentativeRows_numericRouteDescriptors
      formula wellFormed degree isLocal forward nonempty]
    exact paddedCarrierIdentityRepresentativeRows_eq_selectedRows
      period descriptors
  rw [selectedFieldValuesAtPeriod_eq_dedupIdentities_map
    period descriptors field rowsEq]
  rw [paddedCarrierIdentityCandidateStream_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty]
  exact dedup_rankDatumIdentities_map_reconstruct_field
    period descriptors field

end CarrierRankDatumLookup
end LeanTrominoes.PeriodicOrthocrossing
