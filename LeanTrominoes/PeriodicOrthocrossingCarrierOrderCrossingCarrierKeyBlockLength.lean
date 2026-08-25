/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineCandidateExpressionData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierKeyWordRecipeData

/-! # Crossing carrier-key block alignment with order expressions -/

namespace LeanTrominoes.PeriodicOrthocrossing

namespace RouteDescriptorPairAffine

/-- Crossing order expressions and ordinary carrier-key recipes both contain
four entries for every retained shift. -/
theorem occurrencePairCrossingOrderExpressionBlock_length_eq_recipes
    (occurrences : Occurrence × Occurrence) :
    (occurrencePairCrossingOrderExpressionBlock occurrences).length =
      (occurrencePairCrossingCarrierKeyRecipeBlock occurrences).length := by
  unfold occurrencePairCrossingOrderExpressionBlock
    occurrencePairCrossingCarrierKeyRecipeBlock
  have aligned : ∀ shifts : List Cell,
      (shifts.flatMap
        (occurrencePairCrossingOrderExpressionShiftBlock occurrences)).length =
      (shifts.flatMap
        (occurrencePairCrossingCarrierKeyShiftRecipeBlock occurrences)).length := by
    intro shifts
    induction shifts with
    | nil => rfl
    | cons shift shifts induction =>
        simp only [List.flatMap_cons, List.length_append]
        rw [induction]
        rfl
  exact aligned carrierCrossingRetentionShifts

end RouteDescriptorPairAffine

namespace RouteDescriptorOccurrenceSlotCrossing

open RouteDescriptorPairAffine

/-- The flattened crossing expression and carrier-key recipe families have
the same length without evaluating the closed slot table. -/
theorem crossingOrderExpressions_length_eq_carrierKeyRecipes :
    crossingOrderExpressions.length =
      crossingCarrierKeyRecipeBlocks.flatten.length := by
  unfold crossingOrderExpressions crossingOrderExpressionBlocks
    crossingCarrierKeyRecipeBlocks Slot.carrierKeyRecipeBlock
  have aligned : ∀ slots : List Slot,
      (slots.map fun slot =>
          occurrencePairCrossingOrderExpressionBlock
            slot.occurrences).flatten.length =
        (slots.map fun slot =>
          occurrencePairCrossingCarrierKeyRecipeBlock
            slot.occurrences).flatten.length := by
    intro slots
    induction slots with
    | nil => rfl
    | cons slot slots induction =>
        simp only [List.map_cons, List.flatten_cons, List.length_append]
        rw [occurrencePairCrossingOrderExpressionBlock_length_eq_recipes,
          induction]
  exact aligned crossingSlots

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
