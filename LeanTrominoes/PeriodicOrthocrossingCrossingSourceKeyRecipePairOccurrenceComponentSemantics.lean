/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingSourceKeyRecipePairShiftComponentSemantics

/-! # Component semantics of one occurrence-pair crossing block -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairSourceKeyRecipePairs

@[simp] theorem componentRecipeBlock_occurrencePairCrossingSourceKeyRecipePairBlock
    (occurrences : Occurrence × Occurrence) :
    componentRecipeBlock
        (occurrencePairCrossingSourceKeyRecipePairBlock occurrences) =
      occurrencePairCrossingSourceKeyRecipeBlock occurrences := by
  unfold occurrencePairCrossingSourceKeyRecipePairBlock
    occurrencePairCrossingSourceKeyRecipeBlock componentRecipeBlock
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro shift _shiftMember
  exact componentRecipeBlock_occurrencePairCrossingSourceKeyShiftRecipePairBlock
    occurrences shift

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
