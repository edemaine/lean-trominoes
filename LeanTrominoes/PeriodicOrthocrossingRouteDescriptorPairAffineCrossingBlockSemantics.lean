/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingBlocks
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingScanSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCrossingSemantics

/-! # Exact semantics of affine crossing-marker blocks -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

/-- If every descriptor is locally shaped, the affine evaluator produces the
canonical crossing-marker block for every ordered pair. -/
theorem affineCrossingMarkerBlocks_eq_routeDescriptorBlocks
    (marker : α) (descriptors : List RouteDescriptor)
    (allLocal : ∀ descriptor ∈ descriptors,
      RouteDescriptorPairAffine.RouteDescriptor.HasLocalShape descriptor) :
    affineCrossingMarkerBlocks marker descriptors =
      routeDescriptorPairCrossingMarkerBlocks marker descriptors := by
  unfold affineCrossingMarkerBlocks routeDescriptorPairCrossingMarkerBlocks
  apply List.map_congr_left
  intro pair pairMember
  have members := List.mem_product.mp pairMember
  exact affineCrossingMarkers_descriptorPairTokens marker pair
    (allLocal pair.1 members.1) (allLocal pair.2 members.2)

/-- Under the standard stream invariants, the complete affine evaluator emits
thirteen markers for every global oriented crossing. -/
theorem affineCrossingMarkerStream_eq_replicate
    (marker : α) (descriptors : List RouteDescriptor)
    (allLocal : ∀ descriptor ∈ descriptors,
      RouteDescriptorPairAffine.RouteDescriptor.HasLocalShape descriptor)
    (selfIndexed : RouteDescriptorList.SelfIndexed descriptors)
    (commonGrid : RouteDescriptorList.CommonGridSize descriptors) :
    affineCrossingMarkerStream marker descriptors =
      List.replicate
        (13 * routeDescriptorOrientedCrossingCount descriptors) marker := by
  unfold affineCrossingMarkerStream
  rw [affineCrossingMarkerBlocks_eq_routeDescriptorBlocks
    marker descriptors allLocal]
  exact routeDescriptorPairCrossingMarkerBlocks_flatten marker descriptors
    selfIndexed commonGrid

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
