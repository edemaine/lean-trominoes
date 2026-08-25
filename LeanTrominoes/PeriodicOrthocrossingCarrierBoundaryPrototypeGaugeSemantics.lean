/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOwnershipShiftCrossingQuotientSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairRoutePointGaugeQuotientSemantics

/-! # Gauges of normalized crossing-boundary prototypes -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

/-- Translating a crossing by whole periods and then normalizing it recovers
the original crossing when its point is already canonical. -/
theorem crossingRecordPeriodNormalizeAtPeriod_periodTranslate_eq
    {period : Nat} (periodPositive : 0 < period)
    (record : CrossingRecord) (shift : Cell)
    (pointBounds :
      0 ≤ record.point.1 ∧ record.point.1 < period ∧
        0 ≤ record.point.2 ∧ record.point.2 < period) :
    crossingRecordPeriodNormalizeAtPeriod period
        (crossingRecordPeriodTranslateAtPeriod period record shift) =
      record := by
  have shiftEq := crossingRecordPeriodShiftAtPeriod_periodTranslate
    periodPositive record shift pointBounds
  rcases record with
    ⟨first, firstTranslate, second, secondTranslate, point⟩
  rcases shift with ⟨horizontal, vertical⟩
  simp only [crossingRecordPeriodNormalizeAtPeriod]
  rw [shiftEq]
  simp [crossingRecordPeriodTranslateAtPeriod, Cell.add, Cell.sub,
    Cell.scale]

/-- A crossing boundary whose drawing point is canonical has zero physical
macro-grid gauge. -/
theorem carrierPositionGaugeAtPeriod_crossingBoundaryPosition_eq_zero
    {period : Nat} (periodPositive : 0 < period)
    (record : CrossingRecord)
    (pointBounds :
      0 ≤ record.point.1 ∧ record.point.1 < period ∧
        0 ≤ record.point.2 ∧ record.point.2 < period)
    (side : CrossingSide) :
    carrierPositionGaugeAtPeriod period
        (CrossingBoundary.position ⟨record, side⟩) = (0, 0) := by
  have localBounds :
      0 ≤ side.localPosition.1 ∧
        side.localPosition.1 < planarMacroScale ∧
        0 ≤ side.localPosition.2 ∧
        side.localPosition.2 < planarMacroScale := by
    cases side <;>
      norm_num [CrossingSide.localPosition, CrossoverVariable.position,
        planarMacroScale]
  rw [show CrossingBoundary.position ⟨record, side⟩ =
      Cell.add (Cell.scale planarMacroScale record.point)
        side.localPosition by
    rfl]
  rw [carrierPositionGaugeAtPeriod_scale_add_local
    periodPositive record.point side.localPosition localBounds]
  apply Prod.ext
  · exact Int.ediv_eq_zero_of_lt pointBounds.1 pointBounds.2.1
  · exact Int.ediv_eq_zero_of_lt pointBounds.2.2.1 pointBounds.2.2.2

/-- The normalized prototype of a retained translated crossing has zero
physical gauge. -/
theorem carrierPositionGaugeAtPeriod_normalizedCrossingBoundary_eq_zero
    {period : Nat} (periodPositive : 0 < period)
    (record : CrossingRecord) (shift : Cell)
    (pointBounds :
      0 ≤ record.point.1 ∧ record.point.1 < period ∧
        0 ≤ record.point.2 ∧ record.point.2 < period)
    (side : CrossingSide) :
    carrierPositionGaugeAtPeriod period
        (CrossingBoundary.position
          ⟨crossingRecordPeriodNormalizeAtPeriod period
              (crossingRecordPeriodTranslateAtPeriod period record shift),
            side⟩) = (0, 0) := by
  rw [crossingRecordPeriodNormalizeAtPeriod_periodTranslate_eq
    periodPositive record shift pointBounds]
  exact carrierPositionGaugeAtPeriod_crossingBoundaryPosition_eq_zero
    periodPositive record pointBounds side

/-- The complete normalization offset of a retained translated crossing
boundary is exactly its fixed retention shift. -/
theorem carrierNodeNormalizationOffsetAtPeriod_periodTranslatedBoundary
    {period : Nat} (periodPositive : 0 < period)
    (record : CrossingRecord) (shift : Cell)
    (pointBounds :
      0 ≤ record.point.1 ∧ record.point.1 < period ∧
        0 ≤ record.point.2 ∧ record.point.2 < period)
    (side : CrossingSide) :
    carrierNodeNormalizationOffsetAtPeriod period
        (.boundary
          ⟨crossingRecordPeriodTranslateAtPeriod period record shift,
            side⟩) = shift := by
  have ownershipEq := crossingRecordPeriodShiftAtPeriod_periodTranslate
    periodPositive record shift pointBounds
  have gaugeEq :=
    carrierPositionGaugeAtPeriod_normalizedCrossingBoundary_eq_zero
      periodPositive record shift pointBounds side
  simp [carrierNodeNormalizationOffsetAtPeriod,
    carrierNodeRawNormalizationOffsetAtPeriod,
    carrierNodeNormalizedPrototypePositionAtPeriod,
    ownershipEq, gaugeEq, Cell.add]

end LeanTrominoes.PeriodicOrthocrossing
