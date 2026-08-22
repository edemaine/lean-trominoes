/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateBlockData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairDelimiterData
import LeanTrominoes.TM2EndDelimitedBlockMapData

/-! # Pair-stream affine predicate block selection -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- Select fixed predicate-indexed output blocks independently on every
complete tagged descriptor-pair block. -/
def predicateListBlockStream {Output : Type}
    (predicates : List Predicate)
    (blocks : List (List Output))
    (tokens : List RouteDescriptorPairFieldTags.Token) : List Output :=
  TM2EndDelimitedBlockMap.mappedOutput isPairEnd
    (predicateListBlocks predicates blocks) tokens

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
