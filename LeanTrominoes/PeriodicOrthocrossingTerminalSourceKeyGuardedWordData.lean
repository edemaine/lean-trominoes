/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalSourceKeyRecipeData

/-! # Semantic terminal source-key guarded words -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

/-- Doubled guarded source-key components for every padded terminal slot. -/
def terminalSourceKeyGuardedWords
    (tokens : List RouteDescriptorPairFieldTags.Token) : List (List Bool) :=
  RouteDescriptorPairCarrierKeyWordRecipes.words tokens
    (carrierSegmentPredicates.map fun predicate =>
      predicate.evalTokens tokens)
    terminalSourceKeyRecipeBlocks

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
