/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftSlotData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingTruthListCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeActivationCompiler

/-! # Compiled activations for common-shift crossing recipes -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open Computability Turing RouteDescriptorPairCarrierKeyWordRecipes

/-- Expand the complete shifted-slot truth word across its aligned
canonical-left source-key recipe blocks. -/
def canonicalCrossingShiftLeftSourceKeyExpandedActives
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List Bool :=
  compiledExpandedActives canonicalCrossingShiftLeftSourceKeyRecipeBlocks
    (truthValuesFor canonicalCrossingShiftSlots tokens)

noncomputable def canonicalCrossingShiftLeftSourceKeyExpandedActivesComputableInPolyTime :
    TM2ComputableInPolyTime id id
      canonicalCrossingShiftLeftSourceKeyExpandedActives := by
  let composed := TM2CompositionMachine.computableInPolyTime
    (truthValuesForComputableInPolyTime canonicalCrossingShiftSlots)
    (compiledExpandedActivesComputableInPolyTime
      canonicalCrossingShiftLeftSourceKeyRecipeBlocks)
  unfold canonicalCrossingShiftLeftSourceKeyExpandedActives
  exact composed

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing

end
