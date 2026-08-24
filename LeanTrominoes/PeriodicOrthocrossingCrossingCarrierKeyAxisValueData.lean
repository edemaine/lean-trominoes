/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FixedAxisUnaryFields
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierKeyWordRecipeActivationCompiler

/-! # Padded crossing carrier-key axis values -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open RouteDescriptorPairCarrierKeyWordRecipes

/-- Fixed axis bits for one block of oriented-crossing recipes.  Recipes on
the first side are horizontal and recipes on the second side are vertical. -/
def crossingCarrierKeyRecipeAxisBlocks : List (List Bool) :=
  crossingCarrierKeyRecipeBlocks.map fun block =>
    block.map fun recipe => decide (recipe.side = .first)

/-- The blockwise crossing axes in their physical flattened order. -/
def crossingCarrierKeyRecipeAxes : List Bool :=
  crossingCarrierKeyRecipeAxisBlocks.flatten

/-- One zero-or-one axis value for every padded crossing candidate slot. -/
def crossingCarrierKeyAxisValues
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List Nat :=
  FixedAxisUnaryFields.values crossingCarrierKeyRecipeAxes
    (crossingCarrierKeyExpandedActives tokens)

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
