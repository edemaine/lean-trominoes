/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingSourceKeyRecipePairOccurrenceComponentSemantics

/-! # Component semantics of crossing source-key recipe pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open RouteDescriptorPairAffine
open RouteDescriptorPairSourceKeyRecipePairs

@[simp] theorem componentRecipeBlocks_crossingSourceKeyRecipePairBlocks :
    componentRecipeBlocks crossingSourceKeyRecipePairBlocks =
      crossingSourceKeyRecipeBlocks := by
  unfold componentRecipeBlocks crossingSourceKeyRecipePairBlocks
    crossingSourceKeyRecipeBlocks Slot.sourceKeyRecipePairBlock
    Slot.sourceKeyRecipeBlock
  rw [List.map_map]
  apply List.map_congr_left
  intro slot _slotMember
  exact componentRecipeBlock_occurrencePairCrossingSourceKeyRecipePairBlock
    slot.occurrences

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
