/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineTerminalCandidateCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeActivationLength

/-! # Generic length facts for carrier order recipes -/

namespace LeanTrominoes.PeriodicOrthocrossing

namespace RouteDescriptorPairCarrierKeyWordRecipes

/-- Aligned activation and recipe blocks emit exactly one guarded word per
flattened recipe. -/
theorem words_length_of_length_eq
    (tokens : List RouteDescriptorPairFieldTags.Token)
    (actives : List Bool) (blocks : List (List Recipe))
    (lengthEq : actives.length = blocks.length) :
    (words tokens actives blocks).length = blocks.flatten.length := by
  induction actives generalizing blocks with
  | nil =>
      cases blocks with
      | nil => rfl
      | cons block blocks => simp at lengthEq
  | cons active actives induction =>
      cases blocks with
      | nil => simp at lengthEq
      | cons block blocks =>
          simp only [words, List.length_append, List.length_map,
            List.flatten_cons, List.length_cons] at lengthEq ⊢
          rw [induction blocks (by omega)]

end RouteDescriptorPairCarrierKeyWordRecipes

namespace RouteDescriptorPairAffine

@[simp] theorem normalizedFields_length (keepPositive : Bool)
    (expressions : List Expression)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    (normalizedFields keepPositive expressions tokens).length =
      expressions.length := by
  simp [normalizedFields, DelimitedBinaryWordPairExcessMachine.excesses,
    expressionsComparisonInput]

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
