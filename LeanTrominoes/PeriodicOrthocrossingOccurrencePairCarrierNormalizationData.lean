/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairRetainedCarrierRepresentativeData

/-! # Graph-free normalization data for retained carrier pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Physical macro-grid period belonging to a numeric drawing period. -/
def carrierMacroPeriodAtPeriod (period : Nat) : Int :=
  planarMacroScale * period

/-- Canonical lattice-cell quotient of a physical macro-grid position. -/
def carrierPositionGaugeAtPeriod
    (period : Nat) (position : Cell) : Cell :=
  (position.1 / carrierMacroPeriodAtPeriod period,
    position.2 / carrierMacroPeriodAtPeriod period)

/-- Normalize a physical crossing record using only the numeric drawing
period. -/
def crossingRecordPeriodNormalizeAtPeriod
    (period : Nat) (record : CrossingRecord) : CrossingRecord :=
  let shift := crossingRecordPeriodShiftAtPeriod period record
  ⟨record.first, Cell.sub record.firstTranslate shift,
    record.second, Cell.sub record.secondTranslate shift,
    Cell.sub record.point (Cell.scale (period : Int) shift)⟩

/-- The raw occurrence shift extracted while periodically normalizing a
carrier node. -/
def carrierNodeRawNormalizationOffsetAtPeriod
    (period : Nat) : CarrierNode → Cell
  | .terminal terminal => terminal.translate
  | .boundary boundary =>
      crossingRecordPeriodShiftAtPeriod period boundary.crossing

/-- Physical position of the normalized carrier-node prototype. -/
def carrierNodeNormalizedPrototypePositionAtPeriod
    (period : Nat) : CarrierNode → Cell
  | .terminal terminal =>
      segmentTerminalPositionAtPeriod period
        ⟨terminal.indexed, (0, 0), terminal.endpoint⟩
  | .boundary boundary =>
      CrossingBoundary.position
        ⟨crossingRecordPeriodNormalizeAtPeriod
            period boundary.crossing,
          boundary.side⟩

/-- Complete normalized literal offset of a physical carrier node: its raw
periodic occurrence shift plus the canonical gauge of its prototype. -/
def carrierNodeNormalizationOffsetAtPeriod
    (period : Nat) (node : CarrierNode) : Cell :=
  Cell.add (carrierNodeRawNormalizationOffsetAtPeriod period node)
    (carrierPositionGaugeAtPeriod period
      (carrierNodeNormalizedPrototypePositionAtPeriod period node))

/-- Relative normalized offset of the second endpoint of an adjacent pair
from its first endpoint. -/
def carrierNodePairRelativeOffsetAtPeriod
    (period : Nat) (pair : CarrierNode × CarrierNode) : Cell :=
  Cell.sub
    (carrierNodeNormalizationOffsetAtPeriod period pair.2)
    (carrierNodeNormalizationOffsetAtPeriod period pair.1)

/-- Whether a reconstructed carrier pair reaches the next horizontal period
slice after periodic normalization and canonical variable gauging. -/
def carrierNodePairNextSliceAtPeriod
    (period : Nat) (pair : CarrierNode × CarrierNode) : Bool :=
  decide
    (carrierNodePairRelativeOffsetAtPeriod period pair =
      ((1, 0) : Cell))

end LeanTrominoes.PeriodicOrthocrossing
