/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyActiveRecipeData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierKeyWordRecipeData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeyWordRecipeData

/-! # Activity-supported terminal and crossing carrier-key words -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing

namespace RouteDescriptorPairAffine

open RouteDescriptorPairCarrierKeyWordRecipes

/-- One activity-guarded physical carrier-key word per padded terminal node
slot, including slots whose old base-family support bit is false. -/
def terminalActiveCarrierKeyGuardedWords
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List (List Bool) :=
  words tokens (terminalCarrierKeyActivations tokens)
    (forceSupportedBlocks terminalCarrierKeyRecipeBlocks)

end RouteDescriptorPairAffine

namespace RouteDescriptorOccurrenceSlotCrossing

open RouteDescriptorPairCarrierKeyWordRecipes
open RouteDescriptorOccurrenceSlotPairFieldTags

/-- One activity-guarded physical carrier-key word per padded crossing node
slot. -/
def crossingActiveCarrierKeyGuardedWords
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List (List Bool) :=
  words (descriptorTokens tokens) (crossingActivations tokens)
    (forceSupportedBlocks crossingCarrierKeyRecipeBlocks)

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing

end
