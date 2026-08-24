/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeActivationSemantics

/-! # Length of flattened carrier-key recipe activations -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairCarrierKeyWordRecipes

theorem expandedActives_length_of_length_eq
    (actives : List Bool) (blocks : List (List Recipe))
    (lengthEq : actives.length = blocks.length) :
    (expandedActives actives blocks).length = blocks.flatten.length := by
  induction actives generalizing blocks with
  | nil =>
      cases blocks with
      | nil => rfl
      | cons block blocks => simp at lengthEq
  | cons active actives induction =>
      cases blocks with
      | nil => simp at lengthEq
      | cons block blocks =>
          simp only [expandedActives, List.length_append,
            List.length_replicate, List.flatten_cons,
            List.length_cons] at lengthEq ⊢
          rw [induction blocks (by omega)]

end RouteDescriptorPairCarrierKeyWordRecipes
end LeanTrominoes.PeriodicOrthocrossing
