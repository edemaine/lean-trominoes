/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlocks
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyCandidateWordData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairSourceKeyRecipePairData

/-! # Alignment of source-key recipe pairs with carrier-node templates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairSourceKeyRecipePairs

open PaddedSupportedCandidateBlocks
open RouteDescriptorPairCarrierKeyWordRecipes

/-- A recipe pair represents a carrier-node template when its two recovered
keys are exactly the node's compact source-key pair.  Source-key identity
emission deliberately ignores the template's geometric support bit. -/
def MatchesNode (tokens : List RouteDescriptorPairFieldTags.Token)
    (recipes : RecipePair) (template : Template CarrierNode) : Prop :=
  let keys := CarrierNodeSourceKeys.pair template.value
  recipes.1.key tokens = keys.1 ∧
    recipes.2.key tokens = keys.2 ∧
    recipes.1.supported = true ∧ recipes.2.supported = true

end RouteDescriptorPairSourceKeyRecipePairs
end LeanTrominoes.PeriodicOrthocrossing
