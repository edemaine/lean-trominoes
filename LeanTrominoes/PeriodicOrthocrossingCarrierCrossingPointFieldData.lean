/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeRankDatumData

/-! # Signed crossing-point fields of carrier rank data -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierCrossingPointField

inductive Field
  | horizontalPositive
  | horizontalNegative
  | verticalPositive
  | verticalNegative
  deriving DecidableEq, Fintype

def horizontal : Field → Bool
  | .horizontalPositive | .horizontalNegative => true
  | .verticalPositive | .verticalNegative => false

def keepPositive : Field → Bool
  | .horizontalPositive | .verticalPositive => true
  | .horizontalNegative | .verticalNegative => false

def index : Field → Nat
  | .horizontalPositive => 42
  | .horizontalNegative => 43
  | .verticalPositive => 44
  | .verticalNegative => 45

def pointValue (field : Field) (point : Cell) : Nat :=
  let coordinate := if horizontal field then point.1 else point.2
  if keepPositive field then coordinate.toNat else (-coordinate).toNat

def nodeValue (field : Field) : CarrierNode → Nat
  | .terminal _ => 0
  | .boundary boundary => pointValue field boundary.crossing.point

def optionalNodeValue (field : Field) : Option CarrierNode → Nat
  | none => 0
  | some node => nodeValue field node

def rankValue (field : Field) (datum : CarrierNodeRankDatum) : Nat :=
  match datum.boundaryCrossing with
  | none => 0
  | some record => pointValue field record.point

end CarrierCrossingPointField
end LeanTrominoes.PeriodicOrthocrossing
