/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierKeyWordRecipeData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingRecipeActivationCompiler

/-! # Compiler for crossing carrier-key recipe activations -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open Computability Turing

/-- Compiled activation bit for every flattened crossing carrier-key
recipe. -/
def crossingCarrierKeyExpandedActives
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List Bool :=
  compiledRecipeExpandedActives crossingCarrierKeyRecipeBlocks tokens

/-- The fixed crossing carrier-key recipe activation word is
polynomial-time computable. -/
noncomputable def crossingCarrierKeyExpandedActivesComputableInPolyTime :
    TM2ComputableInPolyTime id id crossingCarrierKeyExpandedActives := by
  exact compiledRecipeExpandedActivesComputableInPolyTime
    crossingCarrierKeyRecipeBlocks

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
