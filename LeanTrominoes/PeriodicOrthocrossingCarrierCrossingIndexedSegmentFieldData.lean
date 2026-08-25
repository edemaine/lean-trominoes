/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeRankDatumData

/-! # Indexed-segment fields of carrier crossing records -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierCrossingIndexedSegmentField

inductive SegmentSide
  | first
  | second
  deriving DecidableEq, Fintype

inductive Endpoint
  | start
  | finish
  deriving DecidableEq, Fintype

/-- The first segment index and both segments' signed endpoint coordinates.
The second segment index is already available in its compact source key. -/
inductive Field
  | firstSegmentIndex
  | coordinate (side : SegmentSide) (endpoint : Endpoint)
      (horizontal : Bool) (keepPositive : Bool)
  deriving DecidableEq

def coordinateBase : SegmentSide → Endpoint → Nat
  | .first, .start => 16
  | .first, .finish => 20
  | .second, .start => 30
  | .second, .finish => 34

def coordinateOffset (horizontal keepPositive : Bool) : Nat :=
  if horizontal then
    if keepPositive then 0 else 1
  else if keepPositive then 2 else 3

def index : Field → Nat
  | .firstSegmentIndex => 15
  | .coordinate side endpoint horizontal keepPositive =>
      coordinateBase side endpoint +
        coordinateOffset horizontal keepPositive

def keepPositive : Field → Bool
  | .firstSegmentIndex => true
  | .coordinate _ _ _ keep => keep

def recordSegment (side : SegmentSide)
    (record : CrossingRecordCode) : IndexedGridSegmentCode :=
  match side with
  | .first => record.first
  | .second => record.second

def segmentEndpoint (endpoint : Endpoint)
    (segment : IndexedGridSegmentCode) : Cell :=
  match endpoint with
  | .start => segment.start
  | .finish => segment.finish

def coordinateValue (horizontal keepPositive : Bool)
    (point : Cell) : Nat :=
  let coordinate := if horizontal then point.1 else point.2
  if keepPositive then coordinate.toNat else (-coordinate).toNat

def recordValue (field : Field) (record : CrossingRecordCode) : Nat :=
  match field with
  | .firstSegmentIndex => record.first.segmentIndex
  | .coordinate side endpoint horizontal keep =>
      coordinateValue horizontal keep
        (segmentEndpoint endpoint (recordSegment side record))

def nodeValue (field : Field) : CarrierNode → Nat
  | .terminal _ => 0
  | .boundary boundary => recordValue field boundary.crossing.code

def rankValue (field : Field) (datum : CarrierNodeRankDatum) : Nat :=
  match datum.boundaryCrossing with
  | none => 0
  | some record => recordValue field record

end CarrierCrossingIndexedSegmentField
end LeanTrominoes.PeriodicOrthocrossing
