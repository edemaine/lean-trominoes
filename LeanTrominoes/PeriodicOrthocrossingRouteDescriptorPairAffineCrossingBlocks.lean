/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingScan

/-! # Affine crossing-marker blocks for a route-descriptor stream -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- Run the fixed affine evaluator independently on every row-major ordered
pair of route descriptors. -/
def affineCrossingMarkerBlocks
    (marker : α) (descriptors : List RouteDescriptor) : List (List α) :=
  (descriptors ×ˢ descriptors).map fun pair =>
    affineCrossingMarkers marker (descriptorPairTokens pair)

/-- Flatten the pair-major affine marker blocks. -/
def affineCrossingMarkerStream
    (marker : α) (descriptors : List RouteDescriptor) : List α :=
  (affineCrossingMarkerBlocks marker descriptors).flatten

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
