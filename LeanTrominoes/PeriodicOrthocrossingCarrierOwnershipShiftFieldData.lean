/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeRankDatumData

/-! # Signed ownership-shift fields of carrier rank data -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierOwnershipShiftField

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
  | .horizontalPositive => 46
  | .horizontalNegative => 47
  | .verticalPositive => 48
  | .verticalNegative => 49

def shiftValue (field : Field) (shift : Cell) : Nat :=
  let coordinate := if horizontal field then shift.1 else shift.2
  if keepPositive field then coordinate.toNat else (-coordinate).toNat

def nodeValueAtPeriod (field : Field) (period : Nat) : CarrierNode → Nat
  | .terminal terminal => shiftValue field terminal.translate
  | .boundary boundary =>
      shiftValue field
        (crossingRecordPeriodShiftAtPeriod period boundary.crossing)

def rankValue (field : Field) (datum : CarrierNodeRankDatum) : Nat :=
  shiftValue field datum.ownershipShift

end CarrierOwnershipShiftField
end LeanTrominoes.PeriodicOrthocrossing
