/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineTerminalSemantics
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairRetainedCrossingRecordData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairOccurrenceTemplateSemantics

/-! # Crossing carrier order-coordinate affine semantics -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

@[simp] theorem carrierNode_isHorizontal_boundary_left
    (record : CrossingRecord) :
    (CarrierNode.boundary ⟨record, .left⟩).isHorizontal = true :=
  rfl

@[simp] theorem carrierNode_isHorizontal_boundary_right
    (record : CrossingRecord) :
    (CarrierNode.boundary ⟨record, .right⟩).isHorizontal = true :=
  rfl

@[simp] theorem carrierNode_isHorizontal_boundary_top
    (record : CrossingRecord) :
    (CarrierNode.boundary ⟨record, .top⟩).isHorizontal = false :=
  rfl

@[simp] theorem carrierNode_isHorizontal_boundary_bottom
    (record : CrossingRecord) :
    (CarrierNode.boundary ⟨record, .bottom⟩).isHorizontal = false :=
  rfl

/-- The affine retained crossing point evaluates to the physical point of the
corresponding retained crossing record. -/
theorem occurrencePairCrossingPointAtShift_evalPair
    (occurrences : Occurrence × Occurrence) (shift : Cell)
    (pair : RouteDescriptor × RouteDescriptor) :
    (occurrencePairCrossingPointAtShift occurrences shift).evalPair pair =
      (crossingRecordPeriodTranslateAtPeriod pair.1.gridSize
        (occurrencePairCrossingRecordAtPeriod pair.1.gridSize
          (occurrences.1.evalPair .first pair,
            occurrences.2.evalPair .second pair)) shift).point := by
  unfold occurrencePairCrossingPointAtShift
  rw [Point.evalPair_translateByFirstPeriod]
  rw [Point.evalPair_point]
  have firstSegmentEq :=
    occurrences.1.evalPair_segmentAtFirstPeriod .first pair
  have secondSegmentEq :=
    occurrences.2.evalPair_segmentAtFirstPeriod .second pair
  have firstVerticalEq :
      occurrences.1.segmentAtFirstPeriod.start.vertical.evalPair pair =
        (occurrenceSegmentAtPeriod pair.1.gridSize
          (occurrences.1.evalPair .first pair)).start.2 := by
    simpa [Segment.evalPair, Segment.eval, Point.eval, Expression.evalPair]
      using congrArg (fun segment : GridSegment => segment.start.2)
        firstSegmentEq
  have secondHorizontalEq :
      occurrences.2.segmentAtFirstPeriod.start.horizontal.evalPair pair =
        (occurrenceSegmentAtPeriod pair.1.gridSize
          (occurrences.2.evalPair .second pair)).start.1 := by
    simpa [Segment.evalPair, Segment.eval, Point.eval, Expression.evalPair]
      using congrArg (fun segment : GridSegment => segment.start.1)
        secondSegmentEq
  rw [firstVerticalEq, secondHorizontalEq]
  rfl

/-- Every crossing-boundary affine expression evaluates to the exact
graph-free carrier order coordinate, without additional validity hypotheses. -/
theorem occurrencePairCrossingOrderExpression_evalPair
    (occurrences : Occurrence × Occurrence) (shift : Cell)
    (side : CrossingSide) (pair : RouteDescriptor × RouteDescriptor) :
    (occurrencePairCrossingOrderExpression
        occurrences shift side).evalPair pair =
      carrierNodeOrderCoordinateAtPeriod pair.1.gridSize
        (.boundary
          ⟨crossingRecordPeriodTranslateAtPeriod pair.1.gridSize
              (occurrencePairCrossingRecordAtPeriod pair.1.gridSize
                (occurrences.1.evalPair .first pair,
                  occurrences.2.evalPair .second pair)) shift,
            side⟩) := by
  unfold occurrencePairCrossingOrderExpression
  rw [Expression.evalPair_addConstant, Expression.evalPair_scale]
  have pointEq := occurrencePairCrossingPointAtShift_evalPair
    occurrences shift pair
  cases side with
  | left =>
      change planarMacroScale *
          (occurrencePairCrossingPointAtShift occurrences shift).horizontal.evalPair
            pair + 1 = _
      have coordinateEq :
          (occurrencePairCrossingPointAtShift occurrences shift).horizontal.evalPair
              pair = _ :=
        congrArg Prod.fst pointEq
      rw [coordinateEq]
      simp [carrierNodeOrderCoordinateAtPeriod, carrierNodePositionAtPeriod,
        CrossingBoundary.position, crossingMacroOrigin,
        CrossingSide.localPosition, PlanarThreeSAT.CrossoverVariable.position,
        Cell.add, Cell.scale]
  | right =>
      change planarMacroScale *
          (occurrencePairCrossingPointAtShift occurrences shift).horizontal.evalPair
            pair + 11 = _
      have coordinateEq :
          (occurrencePairCrossingPointAtShift occurrences shift).horizontal.evalPair
              pair = _ :=
        congrArg Prod.fst pointEq
      rw [coordinateEq]
      simp [carrierNodeOrderCoordinateAtPeriod, carrierNodePositionAtPeriod,
        CrossingBoundary.position, crossingMacroOrigin,
        CrossingSide.localPosition, PlanarThreeSAT.CrossoverVariable.position,
        Cell.add, Cell.scale]
  | top =>
      change planarMacroScale *
          (occurrencePairCrossingPointAtShift occurrences shift).vertical.evalPair
            pair + 1 = _
      have coordinateEq :
          (occurrencePairCrossingPointAtShift occurrences shift).vertical.evalPair
              pair = _ :=
        congrArg Prod.snd pointEq
      rw [coordinateEq]
      simp [carrierNodeOrderCoordinateAtPeriod, carrierNodePositionAtPeriod,
        CrossingBoundary.position, crossingMacroOrigin,
        CrossingSide.localPosition, PlanarThreeSAT.CrossoverVariable.position,
        Cell.add, Cell.scale]
  | bottom =>
      change planarMacroScale *
          (occurrencePairCrossingPointAtShift occurrences shift).vertical.evalPair
            pair + 11 = _
      have coordinateEq :
          (occurrencePairCrossingPointAtShift occurrences shift).vertical.evalPair
              pair = _ :=
        congrArg Prod.snd pointEq
      rw [coordinateEq]
      simp [carrierNodeOrderCoordinateAtPeriod, carrierNodePositionAtPeriod,
        CrossingBoundary.position, crossingMacroOrigin,
        CrossingSide.localPosition, PlanarThreeSAT.CrossoverVariable.position,
        Cell.add, Cell.scale]

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
