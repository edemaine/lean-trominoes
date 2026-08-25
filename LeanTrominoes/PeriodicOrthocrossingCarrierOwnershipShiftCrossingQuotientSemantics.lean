/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicIntegerPeriodQuotient
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairRetainedCarrierRepresentativeData
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairRetainedCrossingRecordData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingSlotData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairProjectionSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingSemantics

/-! # Ownership quotients of active retained crossings -/

namespace LeanTrominoes.PeriodicOrthocrossing

theorem crossingRecordPeriodShiftAtPeriod_periodTranslate
    {period : Nat} (periodPositive : 0 < period)
    (record : CrossingRecord) (shift : Cell)
    (pointBounds :
      0 ≤ record.point.1 ∧ record.point.1 < period ∧
        0 ≤ record.point.2 ∧ record.point.2 < period) :
    crossingRecordPeriodShiftAtPeriod period
        (crossingRecordPeriodTranslateAtPeriod period record shift) =
      shift := by
  apply Prod.ext
  · change
      (record.point.1 + (period : Int) * shift.1) / period = shift.1
    exact coordinate_add_period_mul_ediv_eq_shift
      periodPositive pointBounds.1 pointBounds.2.1 shift.1
  · change
      (record.point.2 + (period : Int) * shift.2) / period = shift.2
    exact coordinate_add_period_mul_ediv_eq_shift
      periodPositive pointBounds.2.2.1 pointBounds.2.2.2 shift.2

namespace RouteDescriptorOccurrenceSlotCrossing

open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags
open RouteDescriptorPairAffine

/-- An active fixed crossing slot certifies that its unshifted crossing point
lies in the half-open fundamental square. -/
theorem Slot.crossingPointBounds_of_mem_crossingSlots_of_active
    (slot : Slot) (slotMember : slot ∈ crossingSlots)
    (pair : TaggedDescriptor × TaggedDescriptor)
    (active : slot.evalTokens (descriptorSlotPairTokens pair) = true) :
    let record := occurrencePairCrossingRecordAtPeriod pair.1.1.gridSize
      (slot.occurrences.1.evalPair .first (pair.1.1, pair.2.1),
        slot.occurrences.2.evalPair .second (pair.1.1, pair.2.1))
    0 ≤ record.point.1 ∧ record.point.1 < pair.1.1.gridSize ∧
      0 ≤ record.point.2 ∧ record.point.2 < pair.1.1.gridSize := by
  unfold crossingSlots at slotMember
  rcases List.mem_flatMap.mp slotMember with
    ⟨shapes, _shapesMember, slotMember⟩
  unfold routeShapePairCrossingSlots at slotMember
  rcases List.mem_map.mp slotMember with
    ⟨tagged, _taggedMember, slotEq⟩
  subst slot
  simp only [Slot.evalTokens, Bool.and_eq_true] at active
  have guardedActive := active.1.1
  rw [descriptorTokens_descriptorSlotPairTokens,
    guardedCrossingPredicate_evalTokens] at guardedActive
  simp only [Bool.and_eq_true] at guardedActive
  have crossingActive := guardedActive.2
  rw [evalTokens_crossingPredicate] at crossingActive
  have conditions :
      canonicalOrientedOccurrencePairLinearConditionsAtPeriod
        pair.1.1.gridSize
        (tagged.1.1.evalPair .first (pair.1.1, pair.2.1),
          tagged.2.1.evalPair .second (pair.1.1, pair.2.1)) := by
    simpa [canonicalOrientedOccurrencePairLinearAtPeriod] using
      crossingActive
  simpa [occurrencePairCrossingRecordAtPeriod,
    orientedIntersectionPoint] using
      (show
        0 ≤ (occurrenceSegmentAtPeriod pair.1.1.gridSize
              (tagged.2.1.evalPair .second (pair.1.1, pair.2.1))).start.1 ∧
          (occurrenceSegmentAtPeriod pair.1.1.gridSize
              (tagged.2.1.evalPair .second (pair.1.1, pair.2.1))).start.1 <
            pair.1.1.gridSize ∧
          0 ≤ (occurrenceSegmentAtPeriod pair.1.1.gridSize
              (tagged.1.1.evalPair .first (pair.1.1, pair.2.1))).start.2 ∧
          (occurrenceSegmentAtPeriod pair.1.1.gridSize
              (tagged.1.1.evalPair .first (pair.1.1, pair.2.1))).start.2 <
            pair.1.1.gridSize from
        ⟨conditions.1, conditions.2.1,
          conditions.2.2.1, conditions.2.2.2.1⟩)

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
