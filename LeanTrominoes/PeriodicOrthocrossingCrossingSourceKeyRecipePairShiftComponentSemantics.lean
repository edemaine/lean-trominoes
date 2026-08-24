/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingSourceKeyRecipePairData

/-! # Component semantics of one shifted crossing recipe-pair block -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairSourceKeyRecipePairs

@[simp] theorem componentRecipeBlock_occurrencePairCrossingSourceKeyShiftRecipePairBlock
    (occurrences : Occurrence × Occurrence) (shift : Cell) :
    componentRecipeBlock
        (occurrencePairCrossingSourceKeyShiftRecipePairBlock
          occurrences shift) =
      occurrencePairCrossingSourceKeyShiftRecipeBlock occurrences shift := by
  rfl

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
