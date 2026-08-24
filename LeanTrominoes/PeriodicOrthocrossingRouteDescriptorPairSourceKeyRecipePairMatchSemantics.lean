/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairSourceKeyRecipePairMatchData

/-! # Semantics of one aligned source-key recipe pair -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairSourceKeyRecipePairs

open PaddedSupportedCandidateBlocks
open RouteDescriptorPairCarrierKeyWordRecipes

theorem wordPair_eq_componentPair_activate
    (tokens : List RouteDescriptorPairFieldTags.Token)
    (active : Bool) (recipes : RecipePair)
    (template : Template CarrierNode)
    (aligned : MatchesNode tokens recipes template) :
    wordPair tokens active recipes =
      CarrierNodeSourceKeyCandidateWords.componentPair
        (template.activate active) := by
  rcases aligned with
    ⟨firstValue, secondValue, firstSupported, secondSupported⟩
  cases active <;>
    simp [wordPair, Recipe.word,
      CarrierNodeSourceKeyCandidateWords.componentPair,
      Template.activate, PaddedSupportedCandidateWords.sentinelWord,
      firstValue, secondValue, firstSupported, secondSupported]

end RouteDescriptorPairSourceKeyRecipePairs
end LeanTrominoes.PeriodicOrthocrossing
