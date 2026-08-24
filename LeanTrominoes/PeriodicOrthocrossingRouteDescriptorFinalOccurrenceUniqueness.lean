/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorIndexedSegmentUniqueness

/-! # Occurrence uniqueness from carrier keys -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorCarrierKeyAxisDatum

/-- Indexed-segment membership and equality of complete carrier keys recover
both an indexed segment and an arbitrary final translation. -/
theorem occurrence_eq_of_key_eq
    (descriptors : List RouteDescriptor)
    {first second : IndexedGridSegment × Cell}
    (firstIndexedMember :
      first.1 ∈ routeDescriptorIndexedSegments descriptors)
    (secondIndexedMember :
      second.1 ∈ routeDescriptorIndexedSegments descriptors)
    (keyEq : occurrenceKey first = occurrenceKey second) :
    first = second := by
  have indexedEq : first.1 = second.1 := by
    apply indexedSegment_eq_of_indices_eq descriptors
      firstIndexedMember secondIndexedMember
    · exact congrArg Prod.fst keyEq
    · exact congrArg (fun key => key.2.1) keyEq
  have translateEq : first.2 = second.2 :=
    congrArg (fun key => key.2.2) keyEq
  exact Prod.ext indexedEq translateEq

end RouteDescriptorCarrierKeyAxisDatum
end LeanTrominoes.PeriodicOrthocrossing
