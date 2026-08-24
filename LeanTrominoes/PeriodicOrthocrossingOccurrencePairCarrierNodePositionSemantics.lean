/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierNodePositionData

/-! # Semantics of graph-free occurrence-pair carrier-node positions -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The explicit-period endpoint is the endpoint obtained from the graph's
period translation when the supplied period is its drawing-grid size. -/
theorem segmentTerminalDrawingPointAtPeriod_drawingGridSize
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (terminal : SegmentTerminal) :
    segmentTerminalDrawingPointAtPeriod
        (drawingGridSize graph) terminal =
      terminal.drawingPoint graph := by
  rcases terminal with ⟨indexed, translate, endpoint⟩
  cases endpoint <;>
    simp [segmentTerminalDrawingPointAtPeriod,
      occurrenceSegmentAtPeriod, SegmentTerminal.drawingPoint,
      PeriodicGridDrawing.periodTranslation, drawing_gridSize]

/-- Explicit-period terminal macro positions agree with semantic positions. -/
theorem segmentTerminalPositionAtPeriod_drawingGridSize
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (terminal : SegmentTerminal) :
    segmentTerminalPositionAtPeriod
        (drawingGridSize graph) terminal =
      terminal.position graph := by
  simp only [segmentTerminalPositionAtPeriod, SegmentTerminal.position]
  rw [segmentTerminalDrawingPointAtPeriod_drawingGridSize]

/-- Explicit-period positions agree with semantic positions for both carrier
node constructors. -/
theorem carrierNodePositionAtPeriod_drawingGridSize
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (node : CarrierNode) :
    carrierNodePositionAtPeriod (drawingGridSize graph) node =
      node.position graph := by
  cases node with
  | boundary => rfl
  | terminal terminal =>
      exact segmentTerminalPositionAtPeriod_drawingGridSize graph terminal

/-- The graph-free order coordinate is exactly the coordinate used by the
semantic retained carrier sort. -/
theorem carrierNodeOrderCoordinateAtPeriod_drawingGridSize
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (node : CarrierNode) :
    carrierNodeOrderCoordinateAtPeriod
        (drawingGridSize graph) node =
      node.orderCoordinate graph := by
  unfold carrierNodeOrderCoordinateAtPeriod CarrierNode.orderCoordinate
  rw [carrierNodePositionAtPeriod_drawingGridSize]

end LeanTrominoes.PeriodicOrthocrossing
