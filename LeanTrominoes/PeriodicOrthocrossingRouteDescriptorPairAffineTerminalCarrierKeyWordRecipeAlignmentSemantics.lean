/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeyWordRecipeSemantics

/-! # Alignment of terminal carrier-key recipes and templates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairCarrierKeyWordRecipes
open RouteDescriptorPairFieldTags

/-- Every terminal recipe is aligned with the semantic template obtained
from the same canonical descriptor pair. -/
theorem terminalCarrierKeyRecipeBlocks_match
    (pair : RouteDescriptor × RouteDescriptor) :
    List.Forall₂
      (List.Forall₂ (Recipe.Matches (descriptorPairTokens pair)))
      terminalCarrierKeyRecipeBlocks
      (terminalCarrierKeyTemplateBlocks pair) := by
  rw [← map_map_template_terminalCarrierKeyRecipeBlocks pair]
  induction terminalCarrierKeyRecipeBlocks with
  | nil => exact List.Forall₂.nil
  | cons block blocks induction =>
      apply List.Forall₂.cons
      · induction block with
        | nil => exact List.Forall₂.nil
        | cons recipe recipes induction =>
            exact List.Forall₂.cons
              (recipe.matches_template_descriptorPairTokens pair)
              induction
      · exact induction

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
