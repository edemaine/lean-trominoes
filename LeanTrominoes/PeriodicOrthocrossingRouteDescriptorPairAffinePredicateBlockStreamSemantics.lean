/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateBlockStreamData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairBlockMapSemantics

/-! # Semantics of pair-stream affine predicate block selection -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- On canonical tagged pair records, the block map is exactly the
pair-major concatenation of local selected blocks. -/
@[simp] theorem predicateListBlockStream_encodeDescriptorPairs
    {Output : Type}
    (predicates : List Predicate)
    (blocks : List (List Output))
    (pairs : List (RouteDescriptor × RouteDescriptor)) :
    predicateListBlockStream predicates blocks
        (encodeDescriptorPairs pairs) =
      pairs.flatMap fun pair =>
        predicateListBlocks predicates blocks
          (descriptorPairTokens pair) := by
  unfold predicateListBlockStream
  rw [mappedOutput_encodeDescriptorPairs]

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
