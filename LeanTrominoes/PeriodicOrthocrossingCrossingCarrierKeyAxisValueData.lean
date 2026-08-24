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

/-- The first occurrence of every oriented crossing slot is horizontal and
the second is vertical, so each flattened recipe carries a fixed axis bit. -/
def crossingCarrierKeyRecipeAxes : List Bool :=
  crossingCarrierKeyRecipeBlocks.flatten.map fun recipe =>
    decide (recipe.side = .first)

/-- One zero-or-one axis value for every padded crossing candidate slot. -/
def crossingCarrierKeyAxisValues
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List Nat :=
  FixedAxisUnaryFields.values crossingCarrierKeyRecipeAxes
    (crossingCarrierKeyExpandedActives tokens)

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
