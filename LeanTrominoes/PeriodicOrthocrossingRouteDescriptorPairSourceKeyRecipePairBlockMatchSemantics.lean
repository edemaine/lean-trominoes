/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairSourceKeyRecipePairMatchSemantics

/-! # Semantics of aligned source-key recipe-pair blocks -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairSourceKeyRecipePairs

open PaddedSupportedCandidateBlocks

theorem map_wordPair_eq_map_componentPair_activate
    (tokens : List RouteDescriptorPairFieldTags.Token)
    (active : Bool) (recipes : List RecipePair)
    (templates : List (Template CarrierNode))
    (aligned : List.Forall₂ (MatchesNode tokens) recipes templates) :
    recipes.map (wordPair tokens active) =
      templates.map fun template =>
        CarrierNodeSourceKeyCandidateWords.componentPair
          (template.activate active) := by
  induction recipes generalizing templates with
  | nil =>
      cases aligned
      rfl
  | cons recipe recipes induction =>
      cases templates with
      | nil => cases aligned
      | cons template templates =>
          cases aligned with
          | cons headAligned tailAligned =>
              simp only [List.map_cons]
              rw [wordPair_eq_componentPair_activate
                  tokens active recipe template headAligned,
                induction templates tailAligned]

end RouteDescriptorPairSourceKeyRecipePairs
end LeanTrominoes.PeriodicOrthocrossing
