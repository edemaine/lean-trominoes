/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListDedupMapInjectiveOn
import LeanTrominoes.ListMapZipIdxCongr
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeRankDatumSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalPermutationSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRankOrderedFieldCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRepresentativeFieldLookupSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierNodeCandidateStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierNodeSourceKeyInjectivity
import LeanTrominoes.UnaryPermutationRankBlockLookupSemantics

/-! # Numeric semantics of globally ranked carrier source-key fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSourceKeyRankOrderedFields

open PaddedSupportedLastRepresentativeEqualityRows

private theorem filterMap_sourceKeyCandidates
    (candidates : List (Candidate CarrierNode)) :
    (candidates.map
        CarrierNodeSourceKeyCandidateWords.sourceKeyCandidate).filterMap
          Candidate.value =
      (candidates.filterMap Candidate.value).map
        CarrierNodeSourceKeys.pair := by
  induction candidates with
  | nil => rfl
  | cons candidate candidates induction =>
      rcases candidate with ⟨value, supported⟩
      cases value <;>
        simp [CarrierNodeSourceKeyCandidateWords.sourceKeyCandidate,
          induction]

private theorem flatMap_eq_flatten_map
    {Source Target : Type*} (items : List Source)
    (blocks : Source → List Target) :
    items.flatMap blocks = (items.map blocks).flatten := by
  induction items with
  | nil => rfl
  | cons item items induction =>
      simp only [List.flatMap_cons, List.map_cons, List.flatten_cons,
        induction]

private theorem flatMap_zipIdx_fst
    {Source Target : Type*} (items : List Source)
    (blocks : Source → List Target) :
    items.zipIdx.flatMap (fun entry => blocks entry.1) =
      items.flatMap blocks := by
  have mapped :
      items.zipIdx.map (fun entry => blocks entry.1) =
        items.map blocks :=
    List.map_zipIdx_eq_map_of_mem items
      (fun entry => blocks entry.1) blocks
      (fun _entry _entryMember => rfl)
  rw [flatMap_eq_flatten_map, flatMap_eq_flatten_map, mapped]

private theorem sourcePairValues_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    (paddedCarrierSourceKeyCandidateStream
        (PeriodicCNF.numericRouteDescriptors formula)).filterMap
          Candidate.value =
      (routeDescriptorRetainedCarrierNodesAtPeriod
        (routeDescriptorStreamGridSize
          (PeriodicCNF.numericRouteDescriptors formula))
        (PeriodicCNF.numericRouteDescriptors formula)).map
          CarrierNodeSourceKeys.pair := by
  unfold paddedCarrierSourceKeyCandidateStream
  rw [filterMap_sourceKeyCandidates]
  rw [paddedCarrierNodeCandidateStream_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty]

/-- On valid numeric routes, deduplicated compact source pairs are exactly
the source-pair projection of the deduplicated carrier rank data. -/
theorem sourcePairDedup_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    ((paddedCarrierSourceKeyCandidateStream
        (PeriodicCNF.numericRouteDescriptors formula)).filterMap
          Candidate.value).dedup =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let period := routeDescriptorStreamGridSize descriptors
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod period descriptors).dedup
      datums.map CarrierNodeSourceKeys.datumPair := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let period := routeDescriptorStreamGridSize descriptors
  let nodes := routeDescriptorRetainedCarrierNodesAtPeriod period descriptors
  let datums :=
    (routeDescriptorCarrierRankDatumsAtPeriod period descriptors).dedup
  rw [sourcePairValues_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty]
  change (nodes.map CarrierNodeSourceKeys.pair).dedup =
    datums.map CarrierNodeSourceKeys.datumPair
  rw [List.dedup_map_of_injective_on CarrierNodeSourceKeys.pair nodes
    (sourceKeyPair_injectiveOn_routeDescriptorRetainedCarrierNodesAtPeriod
      period descriptors)]
  unfold datums routeDescriptorCarrierRankDatumsAtPeriod
  rw [List.dedup_map_of_injective_on
    (carrierNodeRankDatumAtPeriod period) nodes
    (fun _first _firstMember _second _secondMember equal =>
      carrierNodeRankDatumAtPeriod_injective period equal)]
  rw [List.map_map]
  apply List.map_congr_left
  intro node _nodeMember
  simp [CarrierNodeSourceKeys.datumPair,
    carrierNodeRankDatumAtPeriod]

/-- The selected physical field blocks are the source-pair blocks of every
deduplicated carrier datum in its original presentation order. -/
theorem selectedFields_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    CarrierSourceKeyRepresentativeFieldLookup.selectedFields
        (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let period := routeDescriptorStreamGridSize descriptors
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod period descriptors).dedup
      datums.zipIdx.flatMap fun entry =>
        CarrierSourceKeyRepresentativeFieldLookup.sourcePairFields
          (some (CarrierNodeSourceKeys.datumPair entry.1)) := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let period := routeDescriptorStreamGridSize descriptors
  let datums :=
    (routeDescriptorCarrierRankDatumsAtPeriod period descriptors).dedup
  rw [CarrierSourceKeyRepresentativeFieldLookup.selectedFields_eq_semanticFields]
  unfold CarrierSourceKeyRepresentativeFieldLookup.semanticFields
  rw [sourcePairDedup_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty]
  change
    (datums.map CarrierNodeSourceKeys.datumPair).flatMap
        (fun sourcePair =>
          CarrierSourceKeyRepresentativeFieldLookup.sourcePairFields
            (some sourcePair)) =
      datums.zipIdx.flatMap fun entry =>
        CarrierSourceKeyRepresentativeFieldLookup.sourcePairFields
          (some (CarrierNodeSourceKeys.datumPair entry.1))
  rw [List.flatMap_map]
  exact (flatMap_zipIdx_fst datums (fun datum =>
    CarrierSourceKeyRepresentativeFieldLookup.sourcePairFields
      (some (CarrierNodeSourceKeys.datumPair datum)))).symm

/-- On valid numeric routes, block permutation emits the twelve source-key
fields in exact global key-major, stable-coordinate carrier order. -/
theorem values_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    values (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let period := routeDescriptorStreamGridSize descriptors
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod period descriptors).dedup
      (CarrierRankGlobal.enumeration datums).flatMap fun entry =>
        CarrierSourceKeyRepresentativeFieldLookup.sourcePairFields
          (some (CarrierNodeSourceKeys.datumPair entry.1)) := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let period := routeDescriptorStreamGridSize descriptors
  let datums :=
    (routeDescriptorCarrierRankDatumsAtPeriod period descriptors).dedup
  have rankEq := CarrierRankGlobal.ranks_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty
  have fieldEq := selectedFields_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty
  have rankIndexEq :
      datums.zipIdx.map (CarrierRankGlobal.rankAt datums) =
        datums.zipIdx.map fun entry =>
          @List.idxOf (CarrierNodeRankDatum × Nat)
            instBEqOfDecidableEq entry
            (CarrierRankGlobal.enumeration datums) := by
    apply List.map_congr_left
    intro entry entryMember
    exact CarrierRankGlobal.rankAt_eq_idxOf_enumeration
      datums entry entryMember
  unfold values
  rw [rankEq, fieldEq, rankIndexEq]
  exact UnaryPermutationRankBlockLookup.values_flatMap_idxOf_of_perm
    datums.zipIdx (CarrierRankGlobal.enumeration datums)
    (CarrierRankGlobal.enumeration_perm_zipIdx datums)
    (CarrierRankGlobal.enumeration_nodup datums)
    (fun entry =>
      CarrierSourceKeyRepresentativeFieldLookup.sourcePairFields
        (some (CarrierNodeSourceKeys.datumPair entry.1)))
    fieldCount
    (fun entry =>
      CarrierSourceKeyRepresentativeFieldLookup.sourcePairFields_length
        (some (CarrierNodeSourceKeys.datumPair entry.1)))

end CarrierSourceKeyRankOrderedFields
end LeanTrominoes.PeriodicOrthocrossing
