/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeRankDatumData

/-! # Normalized carrier order-coordinate fields -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Select the positive or negative unary magnitude of a carrier node's
signed physical order coordinate. -/
def carrierNodeOrderFieldAtPeriod
    (keepPositive : Bool) (period : Nat) (node : CarrierNode) : Nat :=
  if keepPositive then
    (carrierNodeOrderCoordinateAtPeriod period node).toNat
  else
    (-carrierNodeOrderCoordinateAtPeriod period node).toNat

/-- The corresponding field projector on a compiler-facing rank datum. -/
def carrierRankOrderField
    (keepPositive : Bool) (datum : CarrierNodeRankDatum) : Nat :=
  if keepPositive then datum.orderCoordinate.toNat
  else (-datum.orderCoordinate).toNat

@[simp] theorem carrierNodeOrderFieldAtPeriod_true
    (period : Nat) (node : CarrierNode) :
    carrierNodeOrderFieldAtPeriod true period node =
      (carrierNodeOrderCoordinateAtPeriod period node).toNat :=
  rfl

@[simp] theorem carrierNodeOrderFieldAtPeriod_false
    (period : Nat) (node : CarrierNode) :
    carrierNodeOrderFieldAtPeriod false period node =
      (-carrierNodeOrderCoordinateAtPeriod period node).toNat :=
  rfl

@[simp] theorem carrierRankOrderField_true (datum : CarrierNodeRankDatum) :
    carrierRankOrderField true datum = datum.orderCoordinate.toNat :=
  rfl

@[simp] theorem carrierRankOrderField_false (datum : CarrierNodeRankDatum) :
    carrierRankOrderField false datum = (-datum.orderCoordinate).toNat :=
  rfl

end LeanTrominoes.PeriodicOrthocrossing
