/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairFieldValueSemantics

/-! # Canonical templates represented by carrier-key word recipes -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairCarrierKeyWordRecipes

open PaddedSupportedCandidateBlocks
open RouteDescriptorPairFieldTags

/-- Fill a fixed recipe with the stored edge index of its selected descriptor
side to obtain its semantic candidate template. -/
def Recipe.template (pair : RouteDescriptor × RouteDescriptor)
    (recipe : Recipe) : Template CarrierKeyWords.CarrierKey :=
  let routeIndex := match recipe.side with
    | .first => pair.1.edgeIndex
    | .second => pair.2.edgeIndex
  ⟨(routeIndex, recipe.segmentIndex, recipe.translate), recipe.supported⟩

/-- Counting field 2 in a canonical tagged pair block recovers exactly the
route index used by the recipe's semantic template. -/
theorem Recipe.matches_template_descriptorPairTokens
    (pair : RouteDescriptor × RouteDescriptor) (recipe : Recipe) :
    recipe.Matches (descriptorPairTokens pair) (recipe.template pair) := by
  constructor
  · unfold Recipe.key Recipe.template
    rw [tokenFieldValue_descriptorPairTokens]
    rcases pair with ⟨
      ⟨firstVertexCount, firstEdgeCount, firstEdgeIndex,
        firstSourceVertexIndex, firstTargetVertexIndex,
        firstSourcePortRank, firstTargetPortRank,
        ⟨firstHorizontal, firstVertical⟩⟩,
      ⟨secondVertexCount, secondEdgeCount, secondEdgeIndex,
        secondSourceVertexIndex, secondTargetVertexIndex,
        secondSourcePortRank, secondTargetPortRank,
        ⟨secondHorizontal, secondVertical⟩⟩⟩
    cases recipe.side <;>
      simp [pairFieldValue, descriptorFieldValue,
        RouteDescriptor.unaryFields, signedUnaryFields]
  · rfl

end RouteDescriptorPairCarrierKeyWordRecipes
end LeanTrominoes.PeriodicOrthocrossing
