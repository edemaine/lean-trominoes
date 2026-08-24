/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierRepresentativeKeyData
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierKeyLinkEndpoints
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierNodeKeyAxisSemantics

/-! # Descriptor-derived axes of retained carrier links -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

/-- If route descriptors reconstruct a drawing's indexed segments, their
unary value for a retained carrier key is the zero-or-one encoding of every
representative link's physical axis in that key block. -/
theorem retainedRepresentativeCarrierLink_axisValue_of_indexedSegments
    {Vertex : Type} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (descriptors : List RouteDescriptor)
    (indexedSegmentsEq :
      (drawing graph).indexedSegments =
        routeDescriptorIndexedSegments descriptors)
    (key : Nat × Nat × Cell)
    {link : EqualityLink CarrierNode}
    (linkMember :
      link ∈ retainedRepresentativeCarrierLinksAt graph key) :
    RouteDescriptorCarrierKeyAxisDatum.value descriptors (some key) =
      FixedAxisUnaryFields.value true link.first.isHorizontal := by
  have rawLinkMember :
      link ∈ retainedCompleteCarrierLinks graph key :=
    (List.mem_filter.mp linkMember).1
  have endpoints :=
    retainedCompleteCarrierLink_keyBlock_endpoints_mem
      graph key rawLinkMember
  have common :=
    retainedCompleteCarrierLinks_common_key graph key rawLinkMember
  rw [← common.1]
  exact retainedCarrierNode_carrierKey_axisValue
    graph descriptors indexedSegmentsEq endpoints.1

end LeanTrominoes.PeriodicOrthocrossing
