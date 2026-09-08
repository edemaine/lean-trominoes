/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingPointFieldNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCompiledRankOrderedFieldCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCompiledRankOrderedFieldNumericSemantics

/-! # Arbitrary aligned carrier data in exact global rank order -/

noncomputable section
namespace LeanTrominoes.PeriodicOrthocrossing.CarrierSourceKeyRankOrderedValues
open Computability Turing PaddedSupportedLastRepresentativeEqualityRows

abbrev descriptorInputEncoding := CarrierRankDatumCompiledFields.descriptorInputEncoding

/-- Deduplicate an aligned datum column through source keys, then restore global carrier order. -/
def values (alignedValues : List RouteDescriptor → List Nat) (descriptors : List RouteDescriptor) : List Nat :=
  UnaryPermutationRankLookup.values (CarrierRankGlobal.ranks descriptors)
    (CarrierSourceKeyRepresentativeLookup.values (fun source => alignedValues source ++ [0]) descriptors)

private theorem lookup_length (alignedValues : List RouteDescriptor → List Nat)
    (descriptors : List RouteDescriptor) :
    (CarrierSourceKeyRepresentativeLookup.values alignedValues descriptors).length =
      (CarrierRankGlobal.ranks descriptors).length := by
  unfold CarrierSourceKeyRepresentativeLookup.values LastTrueUnaryValueLookupMachine.lookups
  simp only [List.length_map]
  rw [CarrierRankGlobalSuccessor.ranks_length]
  rfl

noncomputable def valuesComputableInPolyTime
    (alignedValues : List RouteDescriptor → List Nat)
    (alignedLength : ∀ descriptors, (alignedValues descriptors ++ [0]).length =
      (paddedCarrierSourceKeyCandidateStream descriptors).length + 1)
    (alignedCompiler : TM2ComputableInPolyTime descriptorInputEncoding UnaryFieldEncoderMachine.unaryFields
      (fun descriptors => alignedValues descriptors ++ [0])) :
    TM2ComputableInPolyTime descriptorInputEncoding UnaryFieldEncoderMachine.unaryFields (values alignedValues) := by
  let selected := CarrierSourceKeyRepresentativeLookup.valuesComputableInPolyTime
    (fun descriptors => alignedValues descriptors ++ [0]) alignedLength alignedCompiler
  unfold values
  exact UnaryPermutationRankLookup.valuesComputableInPolyTime
    descriptorInputEncoding CarrierRankGlobal.ranks
    (CarrierSourceKeyRepresentativeLookup.values (fun descriptors => alignedValues descriptors ++ [0]))
    (lookup_length _) CarrierRankGlobal.ranksComputableInPolyTime selected

/-- Numeric source keys select the datum of the exact retained physical node. -/
theorem selected_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal) (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ [])
    (alignedValues : List RouteDescriptor → List Nat) (datum : CarrierNode → Nat)
    (aligned : List.Forall₂ (fun candidate value => ∀ node,
      candidate.value = some node → value = datum node)
      (paddedCarrierNodeCandidateStream (PeriodicCNF.numericRouteDescriptors formula))
      (alignedValues (PeriodicCNF.numericRouteDescriptors formula))) :
    CarrierSourceKeyRepresentativeLookup.values (fun descriptors => alignedValues descriptors ++ [0])
        (PeriodicCNF.numericRouteDescriptors formula) =
      (routeDescriptorCarrierRankDatumsAtPeriod
        (routeDescriptorStreamGridSize (PeriodicCNF.numericRouteDescriptors formula))
        (PeriodicCNF.numericRouteDescriptors formula)).dedup.map (fun rankDatum => datum rankDatum.identity.node) := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let period := routeDescriptorStreamGridSize descriptors
  let nodeCandidates := paddedCarrierNodeCandidateStream descriptors
  let codeCandidates := nodeCandidates.map
    (Candidate.mapActiveValue CarrierNode.code)
  have activeNodes : nodeCandidates.filterMap Candidate.value =
      routeDescriptorRetainedCarrierNodesAtPeriod period descriptors := by
    unfold nodeCandidates descriptors period
    exact paddedCarrierNodeCandidateStream_numericRouteDescriptors
      formula wellFormed degree isLocal forward nonempty
  have rowsEq : paddedCarrierSourceKeyRepresentativeRows descriptors =
      selectedRows codeCandidates := by
    rw [paddedCarrierSourceKeyRepresentativeRows_eq_selectedRows]
    rw [selectedRows_sourceKeyCandidateStream_eq_identityCandidateStream_numericRouteDescriptors
      formula wellFormed degree isLocal forward nonempty]
    rw [paddedCarrierIdentityCandidateStreamAtPeriod_eq_mapActiveValue]
  have nodeAligned := aligned
  have codeAligned : List.Forall₂
      (fun candidate value => ∀ code,
        candidate.value = some code → value = datum code.node)
      codeCandidates
      (alignedValues descriptors) := by
    exact forall₂_mapActiveValue_code nodeCandidates
      (alignedValues descriptors)
      (datum) nodeAligned
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
          ((alignedValues descriptors ++ [0])) =
        (codeCandidates.filterMap Candidate.value).dedup.map
          (fun code => datum code.node) := by
    exact lookups_selectedRows_selfSupported_aligned_append_value
      codeCandidates
      (alignedValues descriptors)
      supportEq (fun code => datum code.node) codeAligned 0
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
  unfold CarrierSourceKeyRepresentativeLookup.values
  rw [rowsEq, lookupEq, codeValues]
  have reconstruct := dedup_rankDatumIdentities_map_reconstruct_field
    period descriptors (fun rankDatum => datum rankDatum.identity.node)
  simpa [carrierNodeRankDatumAtPeriod, CarrierNodeCode.node_code] using reconstruct


/-- The ordered output is the arbitrary node datum in the same enumeration used by the key compiler. -/
theorem values_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal) (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ [])
    (alignedValues : List RouteDescriptor → List Nat) (datum : CarrierNode → Nat)
    (aligned : List.Forall₂ (fun candidate value => ∀ node,
      candidate.value = some node → value = datum node)
      (paddedCarrierNodeCandidateStream (PeriodicCNF.numericRouteDescriptors formula))
      (alignedValues (PeriodicCNF.numericRouteDescriptors formula))) :
    values alignedValues (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let datums := (routeDescriptorCarrierRankDatumsAtPeriod
        (routeDescriptorStreamGridSize descriptors) descriptors).dedup
      (CarrierRankGlobal.enumeration datums).map fun entry => datum entry.1.identity.node := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let datums := (routeDescriptorCarrierRankDatumsAtPeriod
    (routeDescriptorStreamGridSize descriptors) descriptors).dedup
  have selectedEq := selected_numericRouteDescriptors formula wellFormed degree isLocal forward nonempty
    alignedValues datum aligned
  have rankEq := CarrierRankGlobal.ranks_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty
  have rankIndexEq :
      datums.zipIdx.map (CarrierRankGlobal.rankAt datums) =
        datums.zipIdx.map fun entry =>
          @List.idxOf (CarrierNodeRankDatum × Nat) instBEqOfDecidableEq
            entry (CarrierRankGlobal.enumeration datums) := by
    apply List.map_congr_left
    intro entry member
    exact CarrierRankGlobal.rankAt_eq_idxOf_enumeration datums entry member
  have dataZip : datums.map (fun rankDatum => datum rankDatum.identity.node) =
      datums.zipIdx.map (fun entry => datum entry.1.identity.node) := by
    symm
    exact List.map_zipIdx_eq_map_of_mem datums _ _ (fun _ _ => rfl)
  unfold values
  rw [rankEq, selectedEq, rankIndexEq, dataZip]
  exact UnaryPermutationRankLookup.values_map_idxOf_of_perm
    datums.zipIdx (CarrierRankGlobal.enumeration datums)
    (CarrierRankGlobal.enumeration_perm_zipIdx datums)
    (CarrierRankGlobal.enumeration_nodup datums) (fun entry => datum entry.1.identity.node)

end LeanTrominoes.PeriodicOrthocrossing.CarrierSourceKeyRankOrderedValues
end
