/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierNormalizationData
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierNodePositionSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizationDegree

/-! # Semantics of graph-free retained carrier normalization data -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Numeric crossing normalization agrees with graph-based normalization at
the graph's drawing period. -/
theorem crossingRecordPeriodNormalizeAtPeriod_drawingGridSize
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (record : CrossingRecord) :
    crossingRecordPeriodNormalizeAtPeriod
        (drawingGridSize graph) record =
      record.periodNormalize graph := by
  rcases record with
    ⟨first, firstTranslate, second, secondTranslate, point⟩
  simp [crossingRecordPeriodNormalizeAtPeriod,
    crossingRecordPeriodShiftAtPeriod,
    CrossingRecord.periodNormalize, crossingPeriodShift,
    PeriodicGridDrawing.normalizePoint,
    PeriodicGridDrawing.periodTranslation, drawing_gridSize,
    Cell.sub, Cell.scale]

/-- The graph-free raw endpoint offset is exactly the offset extracted by
carrier-node normalization. -/
theorem carrierNodeRawNormalizationOffsetAtPeriod_drawingGridSize
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (node : CarrierNode) :
    carrierNodeRawNormalizationOffsetAtPeriod
        (drawingGridSize graph) node =
      (normalizeCarrierNode graph node).2 := by
  cases node <;> rfl

/-- The graph-free normalized prototype position is the physical position of
the terminal or canonical boundary prototype used by semantic normalization. -/
theorem carrierNodeNormalizedPrototypePositionAtPeriod_drawingGridSize
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (node : CarrierNode) :
    carrierNodeNormalizedPrototypePositionAtPeriod
        (drawingGridSize graph) node =
      match node with
      | .terminal terminal =>
          SegmentTerminal.position graph
            ⟨terminal.indexed, (0, 0), terminal.endpoint⟩
      | .boundary boundary =>
          (boundary.periodNormalize graph).position := by
  cases node with
  | terminal terminal =>
      exact segmentTerminalPositionAtPeriod_drawingGridSize graph
        ⟨terminal.indexed, (0, 0), terminal.endpoint⟩
  | boundary boundary =>
      simp only [carrierNodeNormalizedPrototypePositionAtPeriod]
      unfold CrossingBoundary.periodNormalize
      rw [crossingRecordPeriodNormalizeAtPeriod_drawingGridSize]

end LeanTrominoes.PeriodicOrthocrossing
