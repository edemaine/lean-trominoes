/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineTerminalAlternativeAlignment
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderCandidateFieldStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderCandidateKeySentinelCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeActivationLength

/-! # Length alignment of carrier order-coordinate candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing

namespace RouteDescriptorPairCarrierKeyWordRecipes

/-- Aligned activation and recipe blocks emit exactly one guarded word per
flattened recipe. -/
theorem words_length_of_length_eq
    (tokens : List RouteDescriptorPairFieldTags.Token)
    (actives : List Bool) (blocks : List (List Recipe))
    (lengthEq : actives.length = blocks.length) :
    (words tokens actives blocks).length = blocks.flatten.length := by
  induction actives generalizing blocks with
  | nil =>
      cases blocks with
      | nil => rfl
      | cons block blocks => simp at lengthEq
  | cons active actives induction =>
      cases blocks with
      | nil => simp at lengthEq
      | cons block blocks =>
          simp only [words, List.length_append, List.length_map,
            List.flatten_cons, List.length_cons] at lengthEq ⊢
          rw [induction blocks (by omega)]

end RouteDescriptorPairCarrierKeyWordRecipes

namespace RouteDescriptorPairAffine

@[simp] theorem normalizedFields_length (keepPositive : Bool)
    (expressions : List Expression)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    (normalizedFields keepPositive expressions tokens).length =
      expressions.length := by
  simp [normalizedFields, DelimitedBinaryWordPairExcessMachine.excesses,
    expressionsComparisonInput]

/-- One direction-split terminal key is emitted for each normalized order
coordinate. -/
theorem terminalDirectionalCarrierKeyGuardedWords_length
    (keepPositive : Bool)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    (terminalDirectionalCarrierKeyGuardedWords tokens).length =
      (terminalDirectionalOrderFields keepPositive tokens).length := by
  unfold terminalDirectionalCarrierKeyGuardedWords
    terminalDirectionalOrderFields
  rw [RouteDescriptorPairCarrierKeyWordRecipes.words_length_of_length_eq]
  · rw [normalizedFields_length,
      terminalDirectionalOrderExpressions_length]
  · rw [List.length_map]
    exact terminalDirectionalPredicates_length

/-- Crossing order expressions and crossing carrier-key recipes contain four
entries for every retained shift. -/
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
open RouteDescriptorPairCarrierKeyWordRecipes

/-- The flattened crossing expression family is aligned with the flattened
crossing carrier-key recipe family without evaluating the closed slot table. -/
theorem crossingOrderExpressions_length_eq_recipes :
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

/-- One guarded crossing key is emitted for each normalized crossing order
coordinate on a canonical tagged descriptor-slot pair. -/
theorem crossingCarrierKeyGuardedWords_length_orderFields
    (keepPositive : Bool)
    (pair : RouteDescriptorOccurrenceSlotBinaryWords.TaggedDescriptor ×
      RouteDescriptorOccurrenceSlotBinaryWords.TaggedDescriptor) :
    (crossingCarrierKeyGuardedWords
        (RouteDescriptorOccurrenceSlotPairFieldTags.descriptorSlotPairTokens
          pair)).length =
      (crossingOrderFields keepPositive
        (RouteDescriptorOccurrenceSlotPairFieldTags.descriptorSlotPairTokens
          pair)).length := by
  unfold crossingCarrierKeyGuardedWords crossingOrderFields
  rw [words_length_of_length_eq]
  · rw [RouteDescriptorPairAffine.normalizedFields_length,
      crossingOrderExpressions_length_eq_recipes]
  · simp [crossingActivations, crossingCarrierKeyRecipeBlocks]

end RouteDescriptorOccurrenceSlotCrossing

namespace TerminalDirectionalCarrierKeyStream

/-- Terminal key and order-value streams remain aligned after concatenating
all descriptor-pair blocks. -/
theorem guardedWords_length_orderFields
    (keepPositive : Bool)
    (pairs : List (RouteDescriptor × RouteDescriptor)) :
    (guardedWords pairs).length =
      (pairs.flatMap fun pair =>
        RouteDescriptorPairAffine.terminalDirectionalOrderFields
          keepPositive
          (RouteDescriptorPairFieldTags.descriptorPairTokens pair)).length := by
  induction pairs with
  | nil => rfl
  | cons pair pairs induction =>
      simp only [guardedWords, List.flatMap_cons, List.length_append]
      change
        (RouteDescriptorPairAffine.terminalDirectionalCarrierKeyGuardedWords
          (RouteDescriptorPairFieldTags.descriptorPairTokens pair)).length +
            (guardedWords pairs).length = _
      rw [RouteDescriptorPairAffine.terminalDirectionalCarrierKeyGuardedWords_length
          keepPositive,
        induction]

end TerminalDirectionalCarrierKeyStream

namespace CrossingCarrierKeyRecipeStream

open RouteDescriptorOccurrenceSlotBinaryWords

/-- Crossing key and order-value streams remain aligned after concatenating
all tagged descriptor-slot pair blocks. -/
theorem guardedWords_length_orderFields
    (keepPositive : Bool)
    (pairs : List (TaggedDescriptor × TaggedDescriptor)) :
    (guardedWords pairs).length =
      (pairs.flatMap fun pair =>
        RouteDescriptorOccurrenceSlotCrossing.crossingOrderFields
          keepPositive
          (RouteDescriptorOccurrenceSlotPairFieldTags.descriptorSlotPairTokens
            pair)).length := by
  induction pairs with
  | nil => rfl
  | cons pair pairs induction =>
      simp only [guardedWords, List.flatMap_cons, List.length_append]
      change
        (RouteDescriptorOccurrenceSlotCrossing.crossingCarrierKeyGuardedWords
          (RouteDescriptorOccurrenceSlotPairFieldTags.descriptorSlotPairTokens
            pair)).length + (guardedWords pairs).length = _
      rw [RouteDescriptorOccurrenceSlotCrossing.crossingCarrierKeyGuardedWords_length_orderFields
          keepPositive,
        induction]

end CrossingCarrierKeyRecipeStream

namespace CarrierOrderCandidateFieldStream

open RouteDescriptorOccurrenceSlotBinaryWords

/-- The combined positive or negative order-coordinate stream has one value
for every guarded carrier-order candidate key. -/
theorem values_length (keepPositive : Bool)
    (descriptors : List RouteDescriptor) :
    (values keepPositive descriptors).length =
      (CarrierOrderCandidateKeyStream.guardedWords descriptors).length := by
  unfold values CarrierOrderCandidateKeyStream.guardedWords
  rw [List.length_append, List.length_append,
    TerminalDirectionalCarrierKeyStream.guardedWords_length_orderFields,
    CrossingCarrierKeyRecipeStream.guardedWords_length_orderFields]

/-- Appending the zero sentinel aligns the values with the rejection-sentinel
key appended before representative selection. -/
theorem valuesWithSentinel_length (keepPositive : Bool)
    (descriptors : List RouteDescriptor) :
    (valuesWithSentinel keepPositive descriptors).length =
      (CarrierOrderCandidateKeyStream.wordsWithSentinel descriptors).words.length := by
  simp [valuesWithSentinel, CarrierOrderCandidateKeyStream.wordsWithSentinel,
    values_length]

end CarrierOrderCandidateFieldStream
end LeanTrominoes.PeriodicOrthocrossing
