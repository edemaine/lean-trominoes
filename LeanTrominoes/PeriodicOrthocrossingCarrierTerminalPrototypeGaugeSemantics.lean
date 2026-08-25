/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairRoutePointGaugeSemantics

/-! # Gauges of normalized carrier-terminal prototypes -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Refining a drawing endpoint to its strictly interior terminal port does
not change its drawing-period gauge. -/
theorem carrierPositionGaugeAtPeriod_segmentTerminalPositionAtPeriod
    {period : Nat} (periodPositive : 0 < period)
    (terminal : SegmentTerminal) :
    carrierPositionGaugeAtPeriod period
        (segmentTerminalPositionAtPeriod period terminal) =
      drawingPointGaugeAtPeriod period
        (segmentTerminalDrawingPointAtPeriod period terminal) := by
  have localBounds := segmentTerminalLocalPosition_in_macrocell
    terminal.indexed.segment terminal.endpoint
  exact carrierPositionGaugeAtPeriod_scale_add_local
    periodPositive _ _
      ⟨le_of_lt localBounds.1, localBounds.2.1,
        le_of_lt localBounds.2.2.1, localBounds.2.2.2⟩

namespace RouteDescriptorPairAffine

/-- The stored endpoint gauge of a gauged affine segment is the exact gauge
of the corresponding normalized carrier-terminal prototype. -/
theorem GaugedSegment.terminalPrototypeGauge_eq
    (gauged : GaugedSegment)
    (pair : RouteDescriptor × RouteDescriptor)
    (correct : gauged.HasPeriodGauges pair)
    (segmentIndex : Nat) (endpoint : SegmentEnd) :
    carrierPositionGaugeAtPeriod pair.1.gridSize
        (segmentTerminalPositionAtPeriod pair.1.gridSize
          ⟨⟨pair.1.edgeIndex, segmentIndex,
              gauged.segment.evalPair pair⟩,
            (0, 0), endpoint⟩) =
      match endpoint with
      | .start => gauged.startGauge
      | .finish => gauged.finishGauge := by
  rw [carrierPositionGaugeAtPeriod_segmentTerminalPositionAtPeriod
    pair.1.gridSize_positive]
  cases endpoint with
  | start =>
      simpa [segmentTerminalDrawingPointAtPeriod,
        occurrenceSegmentAtPeriod, GridSegment.translate,
        Cell.add, Cell.scale, Segment.evalPair, Segment.eval,
        Point.evalPair, Point.HasPeriodGauge] using correct.1
  | finish =>
      simpa [segmentTerminalDrawingPointAtPeriod,
        occurrenceSegmentAtPeriod, GridSegment.translate,
        Cell.add, Cell.scale, Segment.evalPair, Segment.eval,
        Point.evalPair, Point.HasPeriodGauge] using correct.2

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
