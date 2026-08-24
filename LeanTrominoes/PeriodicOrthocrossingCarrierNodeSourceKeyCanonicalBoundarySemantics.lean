/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyTagSemantics
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCrossingRecordData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorFinalOccurrenceUniqueness

/-! # Canonical crossing-boundary uniqueness from compact source keys -/

namespace LeanTrominoes.PeriodicOrthocrossing

open CarrierNodeSourceKeys

/-- For records reconstructed directly from final segment occurrences, the
two source keys and boundary-side tag determine the complete boundary node. -/
theorem canonicalBoundary_eq_of_sourceKeyPair_eq
    (descriptors : List RouteDescriptor) (period : Nat)
    (firstPair secondPair :
      (IndexedGridSegment × Cell) × (IndexedGridSegment × Cell))
    (firstFirstMember :
      firstPair.1.1 ∈ routeDescriptorIndexedSegments descriptors)
    (firstSecondMember :
      firstPair.2.1 ∈ routeDescriptorIndexedSegments descriptors)
    (secondFirstMember :
      secondPair.1.1 ∈ routeDescriptorIndexedSegments descriptors)
    (secondSecondMember :
      secondPair.2.1 ∈ routeDescriptorIndexedSegments descriptors)
    (firstSide secondSide : CrossingSide)
    (equal :
      pair (CarrierNode.boundary
          ⟨occurrencePairCrossingRecordAtPeriod period firstPair,
            firstSide⟩) =
        pair (CarrierNode.boundary
          ⟨occurrencePairCrossingRecordAtPeriod period secondPair,
            secondSide⟩)) :
    CarrierNode.boundary
        ⟨occurrencePairCrossingRecordAtPeriod period firstPair,
          firstSide⟩ =
      CarrierNode.boundary
        ⟨occurrencePairCrossingRecordAtPeriod period secondPair,
          secondSide⟩ := by
  have taggedEqual :
      taggedKey
          (RouteDescriptorCarrierKeyAxisDatum.occurrenceKey firstPair.1)
          (crossingSideTag firstSide) =
        taggedKey
          (RouteDescriptorCarrierKeyAxisDatum.occurrenceKey secondPair.1)
          (crossingSideTag secondSide) := by
    simpa [pair, firstCrossingKey,
      RouteDescriptorCarrierKeyAxisDatum.occurrenceKey,
      occurrencePairCrossingRecordAtPeriod] using congrArg Prod.fst equal
  have recovered := taggedKey_eq _ _ _ _
    (crossingSideTag_lt_eight firstSide)
    (crossingSideTag_lt_eight secondSide) taggedEqual
  have secondKeyEqual :
      RouteDescriptorCarrierKeyAxisDatum.occurrenceKey firstPair.2 =
        RouteDescriptorCarrierKeyAxisDatum.occurrenceKey secondPair.2 := by
    simpa [pair, secondCrossingKey,
      RouteDescriptorCarrierKeyAxisDatum.occurrenceKey,
      occurrencePairCrossingRecordAtPeriod] using congrArg Prod.snd equal
  have firstOccurrenceEqual : firstPair.1 = secondPair.1 :=
    RouteDescriptorCarrierKeyAxisDatum.occurrence_eq_of_key_eq
      descriptors firstFirstMember secondFirstMember recovered.1
  have secondOccurrenceEqual : firstPair.2 = secondPair.2 :=
    RouteDescriptorCarrierKeyAxisDatum.occurrence_eq_of_key_eq
      descriptors firstSecondMember secondSecondMember secondKeyEqual
  have sideEqual : firstSide = secondSide :=
    crossingSideTag_injective recovered.2
  rcases firstPair with ⟨firstFirst, firstSecond⟩
  rcases secondPair with ⟨secondFirst, secondSecond⟩
  simp only at firstOccurrenceEqual secondOccurrenceEqual
  subst secondFirst
  subst secondSecond
  subst secondSide
  rfl

end LeanTrominoes.PeriodicOrthocrossing
