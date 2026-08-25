/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeRankDatumData

/-! # Signed normalization-offset fields of carrier rank data -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierNormalizationOffsetField

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
  | .horizontalPositive => 9
  | .horizontalNegative => 10
  | .verticalPositive => 11
  | .verticalNegative => 12

def offsetValue (field : Field) (offset : Cell) : Nat :=
  let coordinate := if horizontal field then offset.1 else offset.2
  if keepPositive field then coordinate.toNat else (-coordinate).toNat

def nodeValueAtPeriod
    (field : Field) (period : Nat) (node : CarrierNode) : Nat :=
  offsetValue field (carrierNodeNormalizationOffsetAtPeriod period node)

def rankValue (field : Field) (datum : CarrierNodeRankDatum) : Nat :=
  offsetValue field datum.normalizationOffset

end CarrierNormalizationOffsetField
end LeanTrominoes.PeriodicOrthocrossing
