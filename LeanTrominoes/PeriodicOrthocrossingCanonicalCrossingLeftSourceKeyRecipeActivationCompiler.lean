/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingLeftSourceKeyRecipeData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingRecipeActivationCompiler

/-! # Compiled activations for canonical-left crossing recipes -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open Computability Turing RouteDescriptorPairCarrierKeyWordRecipes

def canonicalLeftSourceKeyExpandedActives
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List Bool :=
  compiledRecipeExpandedActives canonicalLeftSourceKeyRecipeBlocks tokens

noncomputable def canonicalLeftSourceKeyExpandedActivesComputableInPolyTime :
    TM2ComputableInPolyTime id id canonicalLeftSourceKeyExpandedActives :=
  compiledRecipeExpandedActivesComputableInPolyTime
    canonicalLeftSourceKeyRecipeBlocks

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing

end
