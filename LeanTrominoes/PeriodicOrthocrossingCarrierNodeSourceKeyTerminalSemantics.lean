/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyTagSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorIndexedSegmentUniqueness

/-! # Terminal-node uniqueness from compact source keys -/

namespace LeanTrominoes.PeriodicOrthocrossing

open CarrierNodeSourceKeys

/-- Among descriptor-reconstructed neighboring occurrences, the tagged
terminal source key determines the complete terminal node. -/
theorem terminal_eq_of_sourceKeyPair_eq
    (descriptors : List RouteDescriptor)
    (first second : IndexedGridSegment × Cell)
    (firstMember : first ∈ routeDescriptorNeighborOccurrences descriptors)
    (secondMember : second ∈ routeDescriptorNeighborOccurrences descriptors)
    (firstEndpoint secondEndpoint : SegmentEnd)
    (equal :
      pair (CarrierNode.terminal
          ⟨first.1, first.2, firstEndpoint⟩) =
        pair (CarrierNode.terminal
          ⟨second.1, second.2, secondEndpoint⟩)) :
    CarrierNode.terminal ⟨first.1, first.2, firstEndpoint⟩ =
      CarrierNode.terminal ⟨second.1, second.2, secondEndpoint⟩ := by
  have taggedEqual :
      taggedKey
          (PeriodicGridDrawing.SegmentOccurrenceKey first.1 first.2)
          (segmentEndTag firstEndpoint) =
        taggedKey
          (PeriodicGridDrawing.SegmentOccurrenceKey second.1 second.2)
          (segmentEndTag secondEndpoint) := by
    simpa [pair, SegmentTerminal.carrierKey] using congrArg Prod.fst equal
  have recovered := taggedKey_eq _ _ _ _
    (segmentEndTag_lt_eight firstEndpoint)
    (segmentEndTag_lt_eight secondEndpoint) taggedEqual
  have indexedEqual : first.1 = second.1 :=
    RouteDescriptorCarrierKeyAxisDatum.indexed_eq_of_occurrenceKey_eq
      descriptors firstMember secondMember (by
        simpa [RouteDescriptorCarrierKeyAxisDatum.occurrenceKey] using
          recovered.1)
  have translateEqual : first.2 = second.2 :=
    congrArg (fun key => key.2.2) recovered.1
  have endpointEqual : firstEndpoint = secondEndpoint :=
    segmentEndTag_injective recovered.2
  rcases first with ⟨firstIndexed, firstTranslate⟩
  rcases second with ⟨secondIndexed, secondTranslate⟩
  simp only at indexedEqual translateEqual
  subst secondIndexed
  subst secondTranslate
  subst secondEndpoint
  rfl

end LeanTrominoes.PeriodicOrthocrossing
