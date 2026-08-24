/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankScanDatumData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorUnaryData

/-! # Fixed unary fields for carrier rank scans -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Four unary naturals encode the positive and negative parts of a cell's
two signed coordinates. -/
def cellUnaryFields (cell : Cell) : List Nat :=
  signedUnaryFields cell.1 ++ signedUnaryFields cell.2

/-- Ten unary naturals encode one proof-free indexed segment. -/
def IndexedGridSegmentCode.scanUnaryFields
    (code : IndexedGridSegmentCode) : List Nat :=
  [code.routeIndex, code.segmentIndex] ++
    cellUnaryFields code.start ++ cellUnaryFields code.finish

/-- Thirty-two unary naturals encode the proof-free identity of one physical
crossing site. -/
def CrossingRecordCode.scanUnaryFields
    (code : CrossingRecordCode) : List Nat :=
  code.first.scanUnaryFields ++
    cellUnaryFields code.firstTranslate ++
    code.second.scanUnaryFields ++
    cellUnaryFields code.secondTranslate ++
    cellUnaryFields code.point

/-- A presence field followed by a fixed thirty-two-field crossing payload.
Absent crossings use an all-zero payload. -/
def optionalCrossingRecordCodeUnaryFields :
    Option CrossingRecordCode → List Nat
  | none => 0 :: List.replicate 32 0
  | some code => 1 :: code.scanUnaryFields

/-- Six unary naturals encode a translated segment-occurrence key. -/
def carrierKeyUnaryFields
    (key : Nat × Nat × Cell) : List Nat :=
  [key.1, key.2.1] ++ cellUnaryFields key.2.2

/-- The fifty fixed downstream fields of one deduplicated carrier rank datum:
carrier key, signed stable-sort coordinate, axis bit, normalized offset,
optional crossover identity, and ownership shift.  The reversible identity is
excluded because representative selection has already removed duplicates. -/
def CarrierRankScanDatum.unaryFields
    (datum : CarrierRankScanDatum) : List Nat :=
  carrierKeyUnaryFields datum.key ++
    signedUnaryFields datum.orderCoordinate ++
    [if datum.horizontal then 1 else 0] ++
    cellUnaryFields datum.normalizationOffset ++
    optionalCrossingRecordCodeUnaryFields datum.boundaryCrossing ++
    cellUnaryFields datum.ownershipShift

/-- The scan fields of a full rank datum after erasing its already-consumed
identity. -/
def CarrierNodeRankDatum.scanUnaryFields
    (datum : CarrierNodeRankDatum) : List Nat :=
  datum.scanDatum.unaryFields

end LeanTrominoes.PeriodicOrthocrossing
