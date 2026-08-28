/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyCanonicalBoundarySemantics
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCanonicalShiftSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorIndexedSegmentUniqueness

/-! # Injectivity of canonical crossing left source keys -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- On the graph-free canonicalized crossing presentation reconstructed from
one descriptor stream, the compact canonical-left pair determines the full
crossing record. -/
theorem crossingPair_injectiveOn_occurrencePairCanonicalizedCrossingHaloAtPeriod
    (period : Nat) (descriptors : List RouteDescriptor) :
    ∀ first ∈ occurrencePairCanonicalizedCrossingHaloAtPeriod period
        (routeDescriptorNeighborOccurrences descriptors),
      ∀ second ∈ occurrencePairCanonicalizedCrossingHaloAtPeriod period
          (routeDescriptorNeighborOccurrences descriptors),
        RetainedCompactAtomWords.crossingPair first =
          RetainedCompactAtomWords.crossingPair second →
        first = second := by
  intro first firstMember second secondMember pairEqual
  unfold occurrencePairCanonicalizedCrossingHaloAtPeriod at firstMember
  unfold occurrencePairCanonicalizedCrossingHaloAtPeriod at secondMember
  rw [List.mem_dedup, List.mem_map] at firstMember secondMember
  rcases firstMember with ⟨firstPair, firstPairMember, firstEqual⟩
  rcases secondMember with ⟨secondPair, secondPairMember, secondEqual⟩
  have firstPairMembers :=
    List.mem_product.mp (List.mem_filter.mp firstPairMember).1
  have secondPairMembers :=
    List.mem_product.mp (List.mem_filter.mp secondPairMember).1
  let firstShift := crossingRecordPeriodShiftAtPeriod period
    (occurrencePairCrossingRecordAtPeriod period firstPair)
  let secondShift := crossingRecordPeriodShiftAtPeriod period
    (occurrencePairCrossingRecordAtPeriod period secondPair)
  let firstCanonicalPair := occurrencePairSubtractShift firstPair firstShift
  let secondCanonicalPair := occurrencePairSubtractShift secondPair secondShift
  have firstRecord :
      occurrencePairCrossingRecordAtPeriod period firstCanonicalPair =
        first := by
    exact
      (occurrencePairCrossingRecordAtPeriod_subtract_periodShift
        period firstPair).trans firstEqual
  have secondRecord :
      occurrencePairCrossingRecordAtPeriod period secondCanonicalPair =
        second := by
    exact
      (occurrencePairCrossingRecordAtPeriod_subtract_periodShift
        period secondPair).trans secondEqual
  have firstFirstIndexed :
      firstCanonicalPair.1.1 ∈
        routeDescriptorIndexedSegments descriptors := by
    simpa [firstCanonicalPair, occurrencePairSubtractShift] using
      RouteDescriptorCarrierKeyAxisDatum.indexed_mem_of_neighbor_mem
        descriptors firstPairMembers.1
  have firstSecondIndexed :
      firstCanonicalPair.2.1 ∈
        routeDescriptorIndexedSegments descriptors := by
    simpa [firstCanonicalPair, occurrencePairSubtractShift] using
      RouteDescriptorCarrierKeyAxisDatum.indexed_mem_of_neighbor_mem
        descriptors firstPairMembers.2
  have secondFirstIndexed :
      secondCanonicalPair.1.1 ∈
        routeDescriptorIndexedSegments descriptors := by
    simpa [secondCanonicalPair, occurrencePairSubtractShift] using
      RouteDescriptorCarrierKeyAxisDatum.indexed_mem_of_neighbor_mem
        descriptors secondPairMembers.1
  have secondSecondIndexed :
      secondCanonicalPair.2.1 ∈
        routeDescriptorIndexedSegments descriptors := by
    simpa [secondCanonicalPair, occurrencePairSubtractShift] using
      RouteDescriptorCarrierKeyAxisDatum.indexed_mem_of_neighbor_mem
        descriptors secondPairMembers.2
  have sourcePairEqual :
      CarrierNodeSourceKeys.pair
          (CarrierNode.boundary
            ⟨occurrencePairCrossingRecordAtPeriod period firstCanonicalPair,
              .left⟩) =
        CarrierNodeSourceKeys.pair
          (CarrierNode.boundary
            ⟨occurrencePairCrossingRecordAtPeriod period secondCanonicalPair,
              .left⟩) := by
    simpa [RetainedCompactAtomWords.crossingPair,
      RetainedCompactAtomWords.carrierPair,
      RetainedCompactAtomWords.zeroCarrierNode,
      firstRecord, secondRecord] using pairEqual
  have boundaryEqual := canonicalBoundary_eq_of_sourceKeyPair_eq
    descriptors period firstCanonicalPair secondCanonicalPair
    firstFirstIndexed firstSecondIndexed
    secondFirstIndexed secondSecondIndexed .left .left sourcePairEqual
  have recordEqual := congrArg
    (fun node => match node with
      | CarrierNode.boundary boundary => boundary.crossing
      | CarrierNode.terminal _ => first)
    boundaryEqual
  simpa [firstRecord, secondRecord] using recordEqual

/-- Consequently the canonical crossing presentation remains duplicate-free
after projection to compact canonical-left source pairs. -/
theorem map_crossingPair_occurrencePairCanonicalizedCrossingHaloAtPeriod_nodup
    (period : Nat) (descriptors : List RouteDescriptor) :
    ((occurrencePairCanonicalizedCrossingHaloAtPeriod period
        (routeDescriptorNeighborOccurrences descriptors)).map
      RetainedCompactAtomWords.crossingPair).Nodup := by
  apply (List.nodup_dedup _).map_on
  intro first firstMember second secondMember equal
  exact crossingPair_injectiveOn_occurrencePairCanonicalizedCrossingHaloAtPeriod
    period descriptors first firstMember second secondMember equal

/-- Stable source-pair deduplication therefore gives the exact compact image
of the canonicalized crossing presentation, with no residual key collision. -/
theorem occurrencePairCanonicalLeftSourceKeyShiftScanDedupAtPeriod_eq_canonicalized
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    (descriptors : List RouteDescriptor)
    (occurrencesEq :
      routeDescriptorNeighborOccurrences descriptors =
        neighborOccurrences graph) :
    occurrencePairCanonicalLeftSourceKeyShiftScanDedupAtPeriod
        (drawingGridSize graph)
        (routeDescriptorNeighborOccurrences descriptors) =
      (occurrencePairCanonicalizedCrossingHaloAtPeriod
        (drawingGridSize graph)
        (routeDescriptorNeighborOccurrences descriptors)).map
          RetainedCompactAtomWords.crossingPair := by
  have mappedNodup :=
    map_crossingPair_occurrencePairCanonicalizedCrossingHaloAtPeriod_nodup
      (drawingGridSize graph) descriptors
  rw [occurrencesEq] at mappedNodup ⊢
  rw [occurrencePairCanonicalLeftSourceKeyShiftScanDedupAtPeriod_eq
    wellFormed degree isLocal]
  exact List.dedup_eq_self.mpr mappedNodup

end LeanTrominoes.PeriodicOrthocrossing
