/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierNormalizationData

/-! # Numeric data needed by rank-major carrier-node compilation -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The proof-free fields needed to rank a carrier node and decide the
metadata bits of a consecutive node pair. -/
structure CarrierNodeRankDatum where
  /-- Finite source identity used only to make datum deduplication exact. -/
  identity : CarrierNode
  key : Nat × Nat × Cell
  orderCoordinate : Int
  horizontal : Bool
  normalizationOffset : Cell
  boundaryCrossing : Option CrossingRecord
  ownershipShift : Cell
  deriving DecidableEq, Repr

/-- Project one physical carrier node to its compiler-facing numeric datum at
an explicit drawing period. -/
def carrierNodeRankDatumAtPeriod
    (period : Nat) (node : CarrierNode) : CarrierNodeRankDatum where
  identity := node
  key := node.carrierKey
  orderCoordinate := carrierNodeOrderCoordinateAtPeriod period node
  horizontal := node.isHorizontal
  normalizationOffset :=
    carrierNodeNormalizationOffsetAtPeriod period node
  boundaryCrossing :=
    match node with
    | .boundary boundary => some boundary.crossing
    | .terminal _ => none
  ownershipShift :=
    match node with
    | .boundary boundary =>
        crossingRecordPeriodShiftAtPeriod period boundary.crossing
    | .terminal terminal => terminal.translate

/-- Whether two numeric node data belong to the same crossover gadget. -/
def CarrierNodeRankDatum.sameCrossoverSite
    (first second : CarrierNodeRankDatum) : Bool :=
  match first.boundaryCrossing, second.boundaryCrossing with
  | some firstCrossing, some secondCrossing =>
      decide (firstCrossing = secondCrossing)
  | _, _ => false

/-- Ownership shift of a numeric adjacent pair, preserving the semantic
priority of the first boundary, then the second boundary, then the first
terminal. -/
def CarrierNodeRankDatum.pairRepresentativeShift
    (first second : CarrierNodeRankDatum) : Cell :=
  match first.boundaryCrossing, second.boundaryCrossing with
  | some _, _ => first.ownershipShift
  | none, some _ => second.ownershipShift
  | none, none => first.ownershipShift

/-- Whether a numeric adjacent pair is the zero-shift representative of its
periodic carrier-link orbit. -/
def CarrierNodeRankDatum.pairIsRepresentative
    (first second : CarrierNodeRankDatum) : Bool :=
  decide (first.pairRepresentativeShift second = (0, 0))

/-- Whether the second numeric node lies one normalized horizontal period
after the first. -/
def CarrierNodeRankDatum.pairNextSlice
    (first second : CarrierNodeRankDatum) : Bool :=
  decide
    (Cell.sub second.normalizationOffset first.normalizationOffset =
      ((1, 0) : Cell))

/-- Axis and next-slice bits contributed by a retained numeric node pair. -/
def CarrierNodeRankDatum.pairBits
    (first second : CarrierNodeRankDatum) : Bool × Bool :=
  (first.horizontal, first.pairNextSlice second)

end LeanTrominoes.PeriodicOrthocrossing
