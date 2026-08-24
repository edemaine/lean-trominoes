/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairRetainedCarrierOrderData

/-! # Graph-free representative retained carrier pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The drawing-period quotient containing a physical crossing point, with
the period supplied as numeric data. -/
def crossingRecordPeriodShiftAtPeriod
    (period : Nat) (record : CrossingRecord) : Cell :=
  (record.point.1 / period, record.point.2 / period)

/-- The ownership shift of an adjacent carrier-node pair, using the same
endpoint priority as semantic retained-link ownership. -/
def carrierNodePairRepresentativeShiftAtPeriod
    (period : Nat) (pair : CarrierNode × CarrierNode) : Cell :=
  match pair.1, pair.2 with
  | .boundary boundary, _ =>
      crossingRecordPeriodShiftAtPeriod period boundary.crossing
  | .terminal _, .boundary boundary =>
      crossingRecordPeriodShiftAtPeriod period boundary.crossing
  | .terminal terminal, .terminal _ => terminal.translate

/-- A reconstructed carrier-node pair owns the zero-shift representative of
its periodic orbit. -/
def CarrierNodePairIsRepresentativeAtPeriod
    (period : Nat) (pair : CarrierNode × CarrierNode) : Prop :=
  carrierNodePairRepresentativeShiftAtPeriod period pair = (0, 0)

instance carrierNodePairIsRepresentativeAtPeriodDecidable
    (period : Nat) (pair : CarrierNode × CarrierNode) :
    Decidable (CarrierNodePairIsRepresentativeAtPeriod period pair) := by
  unfold CarrierNodePairIsRepresentativeAtPeriod
  infer_instance

/-- Exact representative adjacent-node pairs in one reconstructed physical
carrier block. -/
def retainedRepresentativeCarrierNodePairsAtPeriod
    (period : Nat) (nodes : List CarrierNode)
    (key : Nat × Nat × Cell) : List (CarrierNode × CarrierNode) :=
  (retainedCompleteCarrierNodePairsAtPeriod period nodes key).filter
    (CarrierNodePairIsRepresentativeAtPeriod period)

end LeanTrominoes.PeriodicOrthocrossing
