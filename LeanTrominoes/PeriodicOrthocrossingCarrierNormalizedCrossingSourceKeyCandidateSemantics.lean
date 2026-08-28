/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPrototypeGaugeSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedSourceKeyRecipePairMatchSemantics
import LeanTrominoes.PeriodicOrthocrossingCrossingSourceKeyRecipePairMatchSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierNodeData

/-! # Normalized crossing source-key recipes as carrier candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierNormalizedSourceKeyRecipePairs

open PaddedSupportedCandidateBlocks
open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags
open RouteDescriptorPairAffine
open RouteDescriptorPairFieldTags
open RouteDescriptorPairSourceKeyRecipePairs

theorem occurrencePairCrossingSourceKeyRecipePair_matchesNodeAtPeriod
    (pair : RouteDescriptor × RouteDescriptor)
    (occurrences : Occurrence × Occurrence)
    (shift : Cell) (side : CrossingSide) (supported : Bool)
    (pointBounds :
      0 ≤ (occurrencePairCrossingRecordAtPeriod pair.1.gridSize
          (occurrences.1.evalPair .first pair,
            occurrences.2.evalPair .second pair)).point.1 ∧
        (occurrencePairCrossingRecordAtPeriod pair.1.gridSize
          (occurrences.1.evalPair .first pair,
            occurrences.2.evalPair .second pair)).point.1 <
          pair.1.gridSize ∧
        0 ≤ (occurrencePairCrossingRecordAtPeriod pair.1.gridSize
          (occurrences.1.evalPair .first pair,
            occurrences.2.evalPair .second pair)).point.2 ∧
        (occurrencePairCrossingRecordAtPeriod pair.1.gridSize
          (occurrences.1.evalPair .first pair,
            occurrences.2.evalPair .second pair)).point.2 <
          pair.1.gridSize) :
    MatchesNodeAtPeriod (descriptorPairTokens pair) pair.1.gridSize
      (crossingRecipePair shift
        (occurrences.1.taggedSourceKeyRecipeAtShift .first shift side,
          occurrences.2.sourceKeyRecipeAtShift .second shift))
      (⟨CarrierNode.boundary
          ⟨crossingRecordPeriodTranslateAtPeriod pair.1.gridSize
              (occurrencePairCrossingRecordAtPeriod pair.1.gridSize
                (occurrences.1.evalPair .first pair,
                  occurrences.2.evalPair .second pair))
              shift,
            side⟩,
        supported⟩ : Template CarrierNode) := by
  let record := occurrencePairCrossingRecordAtPeriod pair.1.gridSize
    (occurrences.1.evalPair .first pair,
      occurrences.2.evalPair .second pair)
  have normalizeEq :
      crossingRecordPeriodNormalizeAtPeriod pair.1.gridSize
          (crossingRecordPeriodTranslateAtPeriod
            pair.1.gridSize record shift) = record :=
    crossingRecordPeriodNormalizeAtPeriod_periodTranslate_eq
      pair.1.gridSize_positive record shift pointBounds
  have base := occurrencePairCrossingSourceKeyRecipePair_matchesNode
    pair occurrences (0, 0) side supported
  have zeroEq :
      crossingRecordPeriodTranslateAtPeriod pair.1.gridSize
          record (0, 0) = record := by
    rcases record with ⟨first, firstTranslate, second,
      secondTranslate, point⟩
    simp [crossingRecordPeriodTranslateAtPeriod, Cell.add, Cell.scale]
  rw [zeroEq] at base
  unfold MatchesNodeAtPeriod
  simp only [CarrierNodeNormalizedSourceKeys.pairAtPeriod,
    CarrierNodeNormalizedSourceKeys.nodeAtPeriod]
  change _ = (CarrierNodeSourceKeys.pair
      (.boundary ⟨crossingRecordPeriodNormalizeAtPeriod pair.1.gridSize
        (crossingRecordPeriodTranslateAtPeriod pair.1.gridSize record shift),
        side⟩)).1 ∧ _
  rw [normalizeEq]
  simpa [crossingRecipePair,
    CarrierNormalizedSourceKeyRecipes.crossingRecipe,
    Occurrence.taggedSourceKeyRecipeAtShift,
    Occurrence.sourceKeyRecipeAtShift, Cell.add, Cell.sub,
    RouteDescriptorPairSourceKeyRecipePairs.MatchesNode,
    crossingRecordPeriodTranslateAtPeriod] using base

theorem crossingShiftRecipePairBlock_matchesNodeAtPeriod
    (pair : RouteDescriptor × RouteDescriptor)
    (occurrences : Occurrence × Occurrence) (shift : Cell)
    (pointBounds :
      let record := occurrencePairCrossingRecordAtPeriod pair.1.gridSize
        (occurrences.1.evalPair .first pair,
          occurrences.2.evalPair .second pair)
      0 ≤ record.point.1 ∧ record.point.1 < pair.1.gridSize ∧
        0 ≤ record.point.2 ∧ record.point.2 < pair.1.gridSize) :
    List.Forall₂
      (MatchesNodeAtPeriod (descriptorPairTokens pair) pair.1.gridSize)
      (crossingShiftRecipePairBlock occurrences shift)
      (occurrencePairCrossingCarrierNodeShiftTemplateBlock
        pair occurrences shift) := by
  unfold crossingShiftRecipePairBlock
    occurrencePairCrossingSourceKeyShiftRecipePairBlock
    occurrencePairCrossingCarrierNodeShiftTemplateBlock
  dsimp only
  exact List.Forall₂.cons
    (occurrencePairCrossingSourceKeyRecipePair_matchesNodeAtPeriod
      pair occurrences shift .left
      (occurrences.1.carrierKeyAtShiftSupported shift) pointBounds)
    (List.Forall₂.cons
      (occurrencePairCrossingSourceKeyRecipePair_matchesNodeAtPeriod
        pair occurrences shift .right
        (occurrences.1.carrierKeyAtShiftSupported shift) pointBounds)
      (List.Forall₂.cons
        (occurrencePairCrossingSourceKeyRecipePair_matchesNodeAtPeriod
          pair occurrences shift .top
          (occurrences.2.carrierKeyAtShiftSupported shift) pointBounds)
        (List.Forall₂.cons
          (occurrencePairCrossingSourceKeyRecipePair_matchesNodeAtPeriod
            pair occurrences shift .bottom
            (occurrences.2.carrierKeyAtShiftSupported shift) pointBounds)
          List.Forall₂.nil)))

theorem map_crossingShiftRecipePairBlock_words_eq_normalizedCandidates
    (pair : RouteDescriptor × RouteDescriptor)
    (occurrences : Occurrence × Occurrence) (shift : Cell)
    (active : Bool)
    (activeBounds : active = true →
      let record := occurrencePairCrossingRecordAtPeriod pair.1.gridSize
        (occurrences.1.evalPair .first pair,
          occurrences.2.evalPair .second pair)
      0 ≤ record.point.1 ∧ record.point.1 < pair.1.gridSize ∧
        0 ≤ record.point.2 ∧ record.point.2 < pair.1.gridSize) :
    (crossingShiftRecipePairBlock occurrences shift).map
        (wordPair (descriptorPairTokens pair) active) =
      ((occurrencePairCrossingCarrierNodeShiftTemplateBlock
          pair occurrences shift).map (Template.activate active)).map
        (fun candidate =>
          CarrierNodeSourceKeyCandidateWords.componentPair
            (normalizeCandidateAtPeriod pair.1.gridSize candidate)) := by
  cases active with
  | false =>
      unfold crossingShiftRecipePairBlock
        occurrencePairCrossingSourceKeyShiftRecipePairBlock
        occurrencePairCrossingCarrierNodeShiftTemplateBlock
      simp [wordPair, RouteDescriptorPairCarrierKeyWordRecipes.Recipe.word,
        Template.activate, normalizeCandidateAtPeriod,
        PaddedSupportedLastRepresentativeEqualityRows.Candidate.mapValue,
        CarrierNodeSourceKeyCandidateWords.componentPair,
        PaddedSupportedCandidateWords.sentinelWord]
  | true =>
      exact
        map_wordPair_eq_map_componentPair_normalizeCandidateAtPeriod_activate
          (descriptorPairTokens pair) pair.1.gridSize true
          (crossingShiftRecipePairBlock occurrences shift)
          (occurrencePairCrossingCarrierNodeShiftTemplateBlock
            pair occurrences shift)
          (crossingShiftRecipePairBlock_matchesNodeAtPeriod
            pair occurrences shift (activeBounds rfl))

theorem map_crossingRecipePairBlock_words_eq_normalizedCandidates
    (pair : RouteDescriptor × RouteDescriptor)
    (occurrences : Occurrence × Occurrence) (active : Bool)
    (activeBounds : active = true →
      let record := occurrencePairCrossingRecordAtPeriod pair.1.gridSize
        (occurrences.1.evalPair .first pair,
          occurrences.2.evalPair .second pair)
      0 ≤ record.point.1 ∧ record.point.1 < pair.1.gridSize ∧
        0 ≤ record.point.2 ∧ record.point.2 < pair.1.gridSize) :
    (crossingRecipePairBlock occurrences).map
        (wordPair (descriptorPairTokens pair) active) =
      ((occurrencePairCrossingCarrierNodeTemplateBlock
          pair occurrences).map (Template.activate active)).map
        (fun candidate =>
          CarrierNodeSourceKeyCandidateWords.componentPair
            (normalizeCandidateAtPeriod pair.1.gridSize candidate)) := by
  unfold crossingRecipePairBlock
    occurrencePairCrossingCarrierNodeTemplateBlock
  induction carrierCrossingRetentionShifts with
  | nil => rfl
  | cons shift shifts induction =>
      simp only [List.flatMap_cons, List.map_append]
      rw [map_crossingShiftRecipePairBlock_words_eq_normalizedCandidates
          pair occurrences shift active activeBounds,
        induction]

theorem crossingRecipePairWords_eq_normalizedCandidates
    (pair : TaggedDescriptor × TaggedDescriptor) :
    RouteDescriptorPairSourceKeyRecipePairs.words
        (descriptorTokens (descriptorSlotPairTokens pair))
        (RouteDescriptorOccurrenceSlotCrossing.crossingActivations
          (descriptorSlotPairTokens pair))
        crossingRecipePairBlocks =
      (RouteDescriptorOccurrenceSlotCrossing.paddedCrossingCarrierNodeCandidates
        pair).map fun candidate =>
          CarrierNodeSourceKeyCandidateWords.componentPair
            (normalizeCandidateAtPeriod pair.1.1.gridSize candidate) := by
  rw [descriptorTokens_descriptorSlotPairTokens]
  unfold RouteDescriptorOccurrenceSlotCrossing.paddedCrossingCarrierNodeCandidates
    RouteDescriptorOccurrenceSlotCrossing.crossingActivations
    RouteDescriptorOccurrenceSlotCrossing.crossingCarrierNodeTemplateBlocks
    RouteDescriptorOccurrenceSlotCrossing.Slot.carrierNodeTemplateBlock
    crossingRecipePairBlocks
  have aligned : ∀ slots : List RouteDescriptorOccurrenceSlotCrossing.Slot,
      (∀ slot ∈ slots,
        slot ∈ RouteDescriptorOccurrenceSlotCrossing.crossingSlots) →
      RouteDescriptorPairSourceKeyRecipePairs.words
          (descriptorPairTokens (pair.1.1, pair.2.1))
          (slots.map fun slot =>
            slot.evalTokens (descriptorSlotPairTokens pair))
          (slots.map fun slot => crossingRecipePairBlock slot.occurrences) =
        (candidates
          (slots.map fun slot =>
            slot.evalTokens (descriptorSlotPairTokens pair))
          (slots.map fun slot => slot.carrierNodeTemplateBlock
            (pair.1.1, pair.2.1))).map fun candidate =>
              CarrierNodeSourceKeyCandidateWords.componentPair
                (normalizeCandidateAtPeriod
                  pair.1.1.gridSize candidate) := by
    intro slots slotsMember
    induction slots with
    | nil => rfl
    | cons slot slots induction =>
        simp only [List.map_cons,
          RouteDescriptorPairSourceKeyRecipePairs.words, candidates,
          List.map_append]
        rw [map_crossingRecipePairBlock_words_eq_normalizedCandidates]
        · rw [induction fun remaining remainingMember =>
            slotsMember remaining
              (List.mem_cons_of_mem slot remainingMember)]
          simp only [List.map_map, Function.comp_def]
          rfl
        · intro active
          exact slot.crossingPointBounds_of_mem_crossingSlots_of_active
            (slotsMember slot (List.mem_cons_self)) pair active
  exact aligned RouteDescriptorOccurrenceSlotCrossing.crossingSlots
    (fun _ member => member)

end CarrierNormalizedSourceKeyRecipePairs
end LeanTrominoes.PeriodicOrthocrossing
