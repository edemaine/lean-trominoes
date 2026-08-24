/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeRankDatumData

/-! # Identity-free carrier data after representative selection -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Exactly the data still needed after reversible identities have selected
one representative of every carrier node. -/
structure CarrierRankScanDatum where
  key : Nat × Nat × Cell
  orderCoordinate : Int
  horizontal : Bool
  normalizationOffset : Cell
  boundaryCrossing : Option CrossingRecordCode
  ownershipShift : Cell
  deriving DecidableEq, Repr

/-- Erase the identity field after stable duplicate removal. -/
def CarrierNodeRankDatum.scanDatum
    (datum : CarrierNodeRankDatum) : CarrierRankScanDatum where
  key := datum.key
  orderCoordinate := datum.orderCoordinate
  horizontal := datum.horizontal
  normalizationOffset := datum.normalizationOffset
  boundaryCrossing := datum.boundaryCrossing
  ownershipShift := datum.ownershipShift

/-- Whether two selected scan records are ports of the same crossover. -/
def CarrierRankScanDatum.sameCrossoverSite
    (first second : CarrierRankScanDatum) : Bool :=
  match first.boundaryCrossing, second.boundaryCrossing with
  | some firstCrossing, some secondCrossing =>
      decide (firstCrossing = secondCrossing)
  | _, _ => false

/-- Ownership shift of one adjacent selected-record pair. -/
def CarrierRankScanDatum.pairRepresentativeShift
    (first second : CarrierRankScanDatum) : Cell :=
  match first.boundaryCrossing, second.boundaryCrossing with
  | some _, _ => first.ownershipShift
  | none, some _ => second.ownershipShift
  | none, none => first.ownershipShift

/-- Whether an adjacent selected-record pair owns its periodic orbit. -/
def CarrierRankScanDatum.pairIsRepresentative
    (first second : CarrierRankScanDatum) : Bool :=
  decide (first.pairRepresentativeShift second = (0, 0))

/-- Whether the second selected record lies one normalized slice later. -/
def CarrierRankScanDatum.pairNextSlice
    (first second : CarrierRankScanDatum) : Bool :=
  decide
    (Cell.sub second.normalizationOffset first.normalizationOffset =
      ((1, 0) : Cell))

/-- Final axis and next-slice bits of an adjacent selected-record pair. -/
def CarrierRankScanDatum.pairBits
    (first second : CarrierRankScanDatum) : Bool × Bool :=
  (first.horizontal, first.pairNextSlice second)

end LeanTrominoes.PeriodicOrthocrossing
