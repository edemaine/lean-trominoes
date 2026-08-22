/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateBlockData

/-! # Semantics of affine-predicate-selected fixed blocks -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- Fixed block selection consumes exactly the semantic predicate truth word. -/
@[simp] theorem predicateListBlocks_eq
    {Output : Type}
    (predicates : List Predicate)
    (blocks : List (List Output))
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    predicateListBlocks predicates blocks tokens =
      selectTruthBlocks blocks
        (predicates.map fun predicate => predicate.evalTokens tokens) := by
  rw [predicateListBlocks, predicateListTruthValues_eq]

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
