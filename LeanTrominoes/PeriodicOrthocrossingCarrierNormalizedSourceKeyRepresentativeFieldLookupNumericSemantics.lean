/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListDedupMapInjectiveOn
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedSourceKeyIdentityFieldLookupSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyIdentityNumericSelectionSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierIdentityCandidateNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierRankDatumIdentityInjectivity

/-! # Numeric semantics of normalized carrier representative fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierNormalizedSourceKeyRepresentativeFieldLookup

open PaddedSupportedLastRepresentativeEqualityRows

/-- On valid numeric routes, normalized lookup selects the source-pair field
block of every deduplicated carrier rank datum in presentation order. -/
theorem selectedFieldsAtPeriod_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    selectedFieldsAtPeriod
        (routeDescriptorStreamGridSize
          (PeriodicCNF.numericRouteDescriptors formula))
        (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let period := routeDescriptorStreamGridSize descriptors
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod period descriptors).dedup
      datums.flatMap fun datum =>
        CarrierSourceKeyRepresentativeFieldLookup.sourcePairFields
          (some (CarrierNodeNormalizedSourceKeys.datumPairAtPeriod
            period datum)) := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let period := routeDescriptorStreamGridSize descriptors
  let candidates :=
    paddedCarrierIdentityCandidateStreamAtPeriod period descriptors
  have rowsEq :
      paddedCarrierSourceKeyRepresentativeRows descriptors =
        selectedRows candidates := by
    rw [paddedCarrierSourceKeyRepresentativeRows_eq_selectedRows]
    exact
      selectedRows_sourceKeyCandidateStream_eq_identityCandidateStream_numericRouteDescriptors
        formula wellFormed degree isLocal forward nonempty
  have lookupEq := identityFieldLookups period descriptors
  have activeEq :=
    paddedCarrierIdentityCandidateStream_numericRouteDescriptors
      formula wellFormed degree isLocal forward nonempty
  unfold selectedFieldsAtPeriod expandedRows
    CarrierSourceKeyRepresentativeFieldLookup.expandedRows
  rw [rowsEq,
    alignedFieldValuesAtPeriod_eq_identityCandidateFields,
    lookupEq, activeEq]
  rw [List.dedup_map_of_injective_on
    CarrierNodeRankDatum.identity
    (routeDescriptorCarrierRankDatumsAtPeriod period descriptors)
    (carrierRankDatumIdentity_injectiveOn_routeDescriptorRankDatums
      period descriptors)]
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro datum _datumMember
  simp [identityFieldsAtPeriod,
    CarrierNodeNormalizedSourceKeys.datumPairAtPeriod,
    period, descriptors]

end CarrierNormalizedSourceKeyRepresentativeFieldLookup
end LeanTrominoes.PeriodicOrthocrossing
