/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedLastRepresentativeAlignedLookupSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierIdentityCandidateStreamMapSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderRepresentativeLookupNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierOwnershipShiftCandidateAlignmentSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierOwnershipShiftFieldLookupData
import LeanTrominoes.PeriodicOrthocrossingCarrierOwnershipShiftFieldRankSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyIdentityNumericSelectionSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRepresentativeRowSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierNodeCandidateStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierRankDatumIdentityDedupSemantics

/-! # Numeric semantics of carrier ownership-shift lookup -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierOwnershipShiftField

open PaddedSupportedLastRepresentativeEqualityRows

/-- On valid numeric CNF routes, representative lookup returns the selected
ownership-shift magnitude over the stably deduplicated rank data. -/
theorem values_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ [])
    (field : Field) :
    values field (PeriodicCNF.numericRouteDescriptors formula) =
      (routeDescriptorCarrierRankDatumsAtPeriod
        (routeDescriptorStreamGridSize
          (PeriodicCNF.numericRouteDescriptors formula))
        (PeriodicCNF.numericRouteDescriptors formula)).dedup.map
          (rankValue field) := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let period := routeDescriptorStreamGridSize descriptors
  let nodeCandidates := paddedCarrierNodeCandidateStream descriptors
  let codeCandidates := nodeCandidates.map
    (Candidate.mapActiveValue CarrierNode.code)
  have commonPeriod : ∀ descriptor ∈ descriptors,
      descriptor.gridSize = period := by
    intro descriptor descriptorMember
    exact numericRouteDescriptors_gridSize_eq_stream
      formula nonempty descriptor descriptorMember
  have activeNodes : nodeCandidates.filterMap Candidate.value =
      routeDescriptorRetainedCarrierNodesAtPeriod period descriptors := by
    unfold nodeCandidates
    rw [paddedCarrierNodeCandidateStream_numericRouteDescriptors
      formula wellFormed degree isLocal forward nonempty]
  have rowsEq : paddedCarrierSourceKeyRepresentativeRows descriptors =
      selectedRows codeCandidates := by
    rw [paddedCarrierSourceKeyRepresentativeRows_eq_selectedRows]
    rw [selectedRows_sourceKeyCandidateStream_eq_identityCandidateStream_numericRouteDescriptors
      formula wellFormed degree isLocal forward nonempty]
    rw [paddedCarrierIdentityCandidateStreamAtPeriod_eq_mapActiveValue]
  have nodeAligned :=
    CarrierOwnershipShiftCandidateFieldStream.values_forall₂_paddedCarrierNodeCandidateStream
      field period descriptors commonPeriod
  have codeAligned : List.Forall₂
      (fun candidate value => ∀ code,
        candidate.value = some code →
          value = nodeValueAtPeriod field period code.node)
      codeCandidates
      (CarrierOwnershipShiftCandidateFieldStream.values
        field descriptors) := by
    exact forall₂_mapActiveValue_code nodeCandidates
      (CarrierOwnershipShiftCandidateFieldStream.values field descriptors)
      (nodeValueAtPeriod field period) nodeAligned
  have supportEq : ∀ candidate ∈ codeCandidates,
      candidate.supported = candidate.value.isSome := by
    intro candidate candidateMember
    rcases List.mem_map.mp candidateMember with
      ⟨nodeCandidate, _nodeCandidateMember, rfl⟩
    rcases nodeCandidate with ⟨value, supported⟩
    cases value <;> rfl
  have lookupEq :
      LastTrueUnaryValueLookupMachine.lookups
          (selectedRows codeCandidates).words
          (CarrierOwnershipShiftCandidateFieldStream.valuesWithSentinel
            field descriptors) =
        (codeCandidates.filterMap Candidate.value).dedup.map
          (fun code => nodeValueAtPeriod field period code.node) := by
    unfold CarrierOwnershipShiftCandidateFieldStream.valuesWithSentinel
    exact lookups_selectedRows_selfSupported_aligned_append_value
      codeCandidates
      (CarrierOwnershipShiftCandidateFieldStream.values field descriptors)
      supportEq
      (fun code => nodeValueAtPeriod field period code.node)
      codeAligned 0
  have codeValues : codeCandidates.filterMap Candidate.value =
      (routeDescriptorCarrierRankDatumsAtPeriod
        period descriptors).map CarrierNodeRankDatum.identity := by
    calc
      codeCandidates.filterMap Candidate.value =
          (nodeCandidates.filterMap Candidate.value).map
            CarrierNode.code := by
        exact filterMap_mapActiveValue_code nodeCandidates
      _ = (routeDescriptorRetainedCarrierNodesAtPeriod
          period descriptors).map CarrierNode.code := by rw [activeNodes]
      _ = (routeDescriptorCarrierRankDatumsAtPeriod
          period descriptors).map CarrierNodeRankDatum.identity := by
        unfold routeDescriptorCarrierRankDatumsAtPeriod
        rw [List.map_map]
        rfl
  unfold values CarrierSourceKeyRepresentativeLookup.values
  rw [rowsEq, lookupEq, codeValues]
  have reconstruct := dedup_rankDatumIdentities_map_reconstruct_field
    period descriptors (rankValue field)
  simpa using reconstruct

end CarrierOwnershipShiftField
end LeanTrominoes.PeriodicOrthocrossing
