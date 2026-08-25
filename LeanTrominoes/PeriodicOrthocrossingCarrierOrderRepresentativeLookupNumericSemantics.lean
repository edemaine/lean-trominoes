/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedLastRepresentativeAlignedLookupSemantics
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorGridSize
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeCodeSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyActiveCandidateSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderCandidateFieldAlignmentSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderCandidateNodeStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderCandidateNodeWordSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderFieldData
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderRepresentativeLookupData
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyCodeSelectionSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierNodeCandidateStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierRankDatumIdentityDedupSemantics

/-! # Numeric semantics of carrier order-coordinate representative lookup -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedLastRepresentativeEqualityRows

/-- Every numeric route descriptor carries the common period recovered from
the nonempty descriptor stream. -/
theorem numericRouteDescriptors_gridSize_eq_stream
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ [])
    (descriptor : RouteDescriptor)
    (descriptorMember : descriptor ∈
      PeriodicCNF.numericRouteDescriptors formula) :
    descriptor.gridSize =
      routeDescriptorStreamGridSize
        (PeriodicCNF.numericRouteDescriptors formula) := by
  rw [PeriodicCNF.routeDescriptorStreamGridSize_numericRouteDescriptors
    formula nonempty]
  unfold PeriodicCNF.numericRouteDescriptors at descriptorMember
  rcases List.mem_map.mp descriptorMember with
    ⟨tagged, taggedMember, descriptorEq⟩
  subst descriptor
  simp [CNFIncidence.numericRouteDescriptor, RouteDescriptor.gridSize,
    drawingGridSize, PeriodicCNF.incidenceGraph_vertices_length_eq]

/-- Active-node alignment transports through reversible carrier coding. -/
theorem forall₂_mapActiveValue_code
    (candidates : List (Candidate CarrierNode)) (data : List Nat)
    (datum : CarrierNode → Nat)
    (aligned : List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node → value = datum node)
      candidates data) :
    List.Forall₂
      (fun candidate value => ∀ code,
        candidate.value = some code → value = datum code.node)
      (candidates.map (Candidate.mapActiveValue CarrierNode.code)) data := by
  induction aligned with
  | nil => exact List.Forall₂.nil
  | @cons candidate value candidates data headAligned aligned induction =>
      simp only [List.map_cons]
      apply List.Forall₂.cons
      · intro code codeEq
        cases valueEq : candidate.value with
        | none => simp [Candidate.mapActiveValue, valueEq] at codeEq
        | some node =>
            have nodeCodeEq : node.code = code := by
              simpa [Candidate.mapActiveValue, valueEq] using codeEq
            subst code
            simpa using headAligned node valueEq
      · exact induction

theorem filterMap_mapActiveValue_code
    (candidates : List (Candidate CarrierNode)) :
    (candidates.map
        (Candidate.mapActiveValue CarrierNode.code)).filterMap
          Candidate.value =
      (candidates.filterMap Candidate.value).map CarrierNode.code := by
  induction candidates with
  | nil => rfl
  | cons candidate candidates induction =>
      rcases candidate with ⟨value, supported⟩
      cases value <;>
        simp [Candidate.mapActiveValue, induction]

namespace CarrierOrderRepresentativeLookup

/-- On valid numeric CNF routes, representative lookup returns the selected
signed order-coordinate magnitude over the exact stably deduplicated rank
data. -/
theorem values_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ [])
    (keepPositive : Bool) :
    values keepPositive (PeriodicCNF.numericRouteDescriptors formula) =
      (routeDescriptorCarrierRankDatumsAtPeriod
        (routeDescriptorStreamGridSize
          (PeriodicCNF.numericRouteDescriptors formula))
        (PeriodicCNF.numericRouteDescriptors formula)).dedup.map
          (carrierRankOrderField keepPositive) := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let period := routeDescriptorStreamGridSize descriptors
  let nodeCandidates := carrierOrderCandidateNodeStream descriptors
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
    rw [filterMap_carrierOrderCandidateNodeStream]
    exact paddedCarrierNodeCandidateStream_numericRouteDescriptors
      formula wellFormed degree isLocal forward nonempty
  have sourceCandidatesEq :
      nodeCandidates.map
          CarrierNodeSourceKeyCandidateWords.sourceKeyCandidate =
        nodeCandidates.map
          (Candidate.mapActiveValue CarrierNodeSourceKeys.pair) := by
    apply List.map_congr_left
    intro candidate _candidateMember
    exact
      CarrierNodeSourceKeyCandidateWords.sourceKeyCandidate_eq_mapActiveValue
        candidate
  have rowsEq : CarrierOrderRepresentativeRows.rows descriptors =
      selectedRows codeCandidates := by
    rw [CarrierOrderRepresentativeRows.rows_eq_selectedRows_carrierOrderCandidateNodeStream]
    rw [sourceCandidatesEq]
    exact selectedRows_sourceKey_eq_code_of_filterMap_eq_retainedCarrierNodes
      period descriptors nodeCandidates activeNodes
  have nodeAligned :=
    CarrierOrderCandidateFieldStream.values_forall₂_carrierOrderCandidateNodeStream
      keepPositive period descriptors commonPeriod
  have codeAligned : List.Forall₂
      (fun candidate value => ∀ code,
        candidate.value = some code →
          value = carrierNodeOrderFieldAtPeriod
            keepPositive period code.node)
      codeCandidates
      (CarrierOrderCandidateFieldStream.values
        keepPositive descriptors) := by
    exact forall₂_mapActiveValue_code nodeCandidates
      (CarrierOrderCandidateFieldStream.values keepPositive descriptors)
      (carrierNodeOrderFieldAtPeriod keepPositive period) nodeAligned
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
          (CarrierOrderCandidateFieldStream.valuesWithSentinel
            keepPositive descriptors) =
        (codeCandidates.filterMap Candidate.value).dedup.map
          (fun code => carrierNodeOrderFieldAtPeriod
            keepPositive period code.node) := by
    unfold CarrierOrderCandidateFieldStream.valuesWithSentinel
    exact lookups_selectedRows_selfSupported_aligned_append_value
      codeCandidates
      (CarrierOrderCandidateFieldStream.values keepPositive descriptors)
      supportEq
      (fun code => carrierNodeOrderFieldAtPeriod
        keepPositive period code.node)
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
  unfold values
  rw [rowsEq, lookupEq, codeValues]
  have reconstruct := dedup_rankDatumIdentities_map_reconstruct_field
    period descriptors (carrierRankOrderField keepPositive)
  cases keepPositive <;>
    simpa [carrierNodeOrderFieldAtPeriod, carrierRankOrderField,
      carrierNodeRankDatumAtPeriod] using reconstruct

end CarrierOrderRepresentativeLookup
end LeanTrominoes.PeriodicOrthocrossing
