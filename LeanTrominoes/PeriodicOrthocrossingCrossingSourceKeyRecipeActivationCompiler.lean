/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingRecipeActivationCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingSourceKeyRecipeData

/-! # Compiled activations for doubled crossing source-key recipes -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open Computability Turing RouteDescriptorPairCarrierKeyWordRecipes

def crossingSourceKeyExpandedActives
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List Bool :=
  compiledRecipeExpandedActives crossingSourceKeyRecipeBlocks tokens

noncomputable def crossingSourceKeyExpandedActivesComputableInPolyTime :
    TM2ComputableInPolyTime id id crossingSourceKeyExpandedActives :=
  compiledRecipeExpandedActivesComputableInPolyTime
    crossingSourceKeyRecipeBlocks

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing

end
