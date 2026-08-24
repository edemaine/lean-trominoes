/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairRetainedCarrierNodeData

/-! # Graph-free positions of occurrence-pair carrier nodes -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The translated drawing-grid endpoint of a terminal, using an explicit
numeric drawing period instead of a periodic graph. -/
def segmentTerminalDrawingPointAtPeriod
    (period : Nat) (terminal : SegmentTerminal) : Cell :=
  let translated := occurrenceSegmentAtPeriod period
    (terminal.indexed, terminal.translate)
  match terminal.endpoint with
  | .start => translated.start
  | .finish => translated.finish

/-- The absolute macro-grid position of a terminal at an explicit period. -/
def segmentTerminalPositionAtPeriod
    (period : Nat) (terminal : SegmentTerminal) : Cell :=
  Cell.add
    (Cell.scale planarMacroScale
      (segmentTerminalDrawingPointAtPeriod period terminal))
    (segmentTerminalLocalPosition
      terminal.indexed.segment terminal.endpoint)

/-- The absolute macro-grid position of either kind of carrier node at an
explicit period.  Boundary positions already contain their physical crossing
point and therefore do not depend on the period. -/
def carrierNodePositionAtPeriod
    (period : Nat) : CarrierNode → Cell
  | .boundary boundary => boundary.position
  | .terminal terminal =>
      segmentTerminalPositionAtPeriod period terminal

/-- The physical coordinate used to sort a carrier node along its axis, with
the drawing period supplied as numeric data. -/
def carrierNodeOrderCoordinateAtPeriod
    (period : Nat) (node : CarrierNode) : Int :=
  if node.isHorizontal then
    (carrierNodePositionAtPeriod period node).1
  else
    (carrierNodePositionAtPeriod period node).2

end LeanTrominoes.PeriodicOrthocrossing
