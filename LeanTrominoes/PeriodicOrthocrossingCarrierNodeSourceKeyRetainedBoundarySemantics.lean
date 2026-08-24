/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyCanonicalBoundarySemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyCrossingRecordSemantics

/-! # Retained crossing-boundary uniqueness from compact source keys -/

namespace LeanTrominoes.PeriodicOrthocrossing

open CarrierNodeSourceKeys

/-- The compact source-key pair distinguishes retained translated boundaries
whose source occurrences belong to one route-descriptor stream. -/
theorem retainedBoundary_eq_of_sourceKeyPair_eq
    (descriptors : List RouteDescriptor) (period : Nat)
    (firstPair secondPair :
      (IndexedGridSegment × Cell) × (IndexedGridSegment × Cell))
    (firstFirstMember :
      firstPair.1 ∈ routeDescriptorNeighborOccurrences descriptors)
    (firstSecondMember :
      firstPair.2 ∈ routeDescriptorNeighborOccurrences descriptors)
    (secondFirstMember :
      secondPair.1 ∈ routeDescriptorNeighborOccurrences descriptors)
    (secondSecondMember :
      secondPair.2 ∈ routeDescriptorNeighborOccurrences descriptors)
    (firstShift secondShift : Cell)
    (firstSide secondSide : CrossingSide)
    (equal :
      pair (CarrierNode.boundary
          ⟨crossingRecordPeriodTranslateAtPeriod period
              (occurrencePairCrossingRecordAtPeriod period firstPair)
              firstShift,
            firstSide⟩) =
        pair (CarrierNode.boundary
          ⟨crossingRecordPeriodTranslateAtPeriod period
              (occurrencePairCrossingRecordAtPeriod period secondPair)
              secondShift,
            secondSide⟩)) :
    CarrierNode.boundary
        ⟨crossingRecordPeriodTranslateAtPeriod period
            (occurrencePairCrossingRecordAtPeriod period firstPair)
            firstShift,
          firstSide⟩ =
      CarrierNode.boundary
        ⟨crossingRecordPeriodTranslateAtPeriod period
            (occurrencePairCrossingRecordAtPeriod period secondPair)
            secondShift,
          secondSide⟩ := by
  rw [crossingRecordPeriodTranslateAtPeriod_occurrencePairCrossingRecord,
    crossingRecordPeriodTranslateAtPeriod_occurrencePairCrossingRecord]
      at equal ⊢
  apply canonicalBoundary_eq_of_sourceKeyPair_eq
    descriptors period _ _
  · exact RouteDescriptorCarrierKeyAxisDatum.indexed_mem_of_neighbor_mem
      descriptors (occurrence := firstPair.1) firstFirstMember
  · exact RouteDescriptorCarrierKeyAxisDatum.indexed_mem_of_neighbor_mem
      descriptors (occurrence := firstPair.2) firstSecondMember
  · exact RouteDescriptorCarrierKeyAxisDatum.indexed_mem_of_neighbor_mem
      descriptors (occurrence := secondPair.1) secondFirstMember
  · exact RouteDescriptorCarrierKeyAxisDatum.indexed_mem_of_neighbor_mem
      descriptors (occurrence := secondPair.2) secondSecondMember
  · exact equal

end LeanTrominoes.PeriodicOrthocrossing
