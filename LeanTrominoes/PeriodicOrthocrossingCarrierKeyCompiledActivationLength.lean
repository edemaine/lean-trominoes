/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeActivationCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeActivationLength

/-! # Length of compiled flattened carrier-recipe activations -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairCarrierKeyWordRecipes

/-- Exact-length block activations compile to one bit per flattened recipe. -/
theorem compiledExpandedActives_length_of_length_eq
    (blocks : List (List Recipe)) (actives : List Bool)
    (lengthEq : actives.length = blocks.length) :
    (compiledExpandedActives blocks actives).length =
      blocks.flatten.length := by
  rw [compiledExpandedActives_eq blocks actives lengthEq]
  exact expandedActives_length_of_length_eq actives blocks lengthEq

end RouteDescriptorPairCarrierKeyWordRecipes
end LeanTrominoes.PeriodicOrthocrossing
