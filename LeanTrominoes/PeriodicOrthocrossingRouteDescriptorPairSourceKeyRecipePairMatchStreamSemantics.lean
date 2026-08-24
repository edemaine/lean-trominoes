/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairSourceKeyRecipePairBlockMatchSemantics

/-! # Semantics of aligned source-key recipe-pair streams -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairSourceKeyRecipePairs

open PaddedSupportedCandidateBlocks

theorem words_eq_map_componentPair_candidates
    (tokens : List RouteDescriptorPairFieldTags.Token)
    (actives : List Bool) (recipeBlocks : List (List RecipePair))
    (templateBlocks : List (List (Template CarrierNode)))
    (aligned : List.Forall₂
      (List.Forall₂ (MatchesNode tokens))
      recipeBlocks templateBlocks) :
    words tokens actives recipeBlocks =
      (candidates actives templateBlocks).map
        CarrierNodeSourceKeyCandidateWords.componentPair := by
  induction actives generalizing recipeBlocks templateBlocks with
  | nil => rfl
  | cons active actives induction =>
      cases recipeBlocks with
      | nil =>
          cases aligned
          rfl
      | cons recipes recipeBlocks =>
          cases templateBlocks with
          | nil => cases aligned
          | cons templates templateBlocks =>
              cases aligned with
              | cons headAligned tailAligned =>
                  rw [words, candidates, List.map_append,
                    map_wordPair_eq_map_componentPair_activate
                      tokens active recipes templates headAligned,
                    induction recipeBlocks templateBlocks tailAligned]
                  simp only [List.map_map, Function.comp_def]

end RouteDescriptorPairSourceKeyRecipePairs
end LeanTrominoes.PeriodicOrthocrossing
