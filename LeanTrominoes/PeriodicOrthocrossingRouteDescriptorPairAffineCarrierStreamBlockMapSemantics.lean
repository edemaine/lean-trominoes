/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCarrierSegmentScanData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateBlockStreamSemantics

/-! # Canonical block-map semantics of affine carrier candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- On canonical tagged pair records, the carrier candidate scan is the
pair-major concatenation of its local affine blocks. -/
@[simp] theorem affineCarrierSegmentBitStream_encodeDescriptorPairs
    (pairs : List (RouteDescriptor × RouteDescriptor)) :
    affineCarrierSegmentBitStream (encodeDescriptorPairs pairs) =
      pairs.flatMap fun pair =>
        affineCarrierSegmentBitBlock (descriptorPairTokens pair) := by
  unfold affineCarrierSegmentBitStream affineCarrierSegmentBitBlock
  rw [predicateListBlockStream_encodeDescriptorPairs]

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
