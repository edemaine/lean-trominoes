/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyFieldData

/-! # Selected signed-coordinate carrier-key fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeySignedFields

def horizontalPositiveValues (descriptors : List RouteDescriptor) : List Nat :=
  CarrierRankKeyField.values .horizontalPositive descriptors

def horizontalNegativeValues (descriptors : List RouteDescriptor) : List Nat :=
  CarrierRankKeyField.values .horizontalNegative descriptors

def verticalPositiveValues (descriptors : List RouteDescriptor) : List Nat :=
  CarrierRankKeyField.values .verticalPositive descriptors

def verticalNegativeValues (descriptors : List RouteDescriptor) : List Nat :=
  CarrierRankKeyField.values .verticalNegative descriptors

end CarrierRankKeySignedFields
end LeanTrominoes.PeriodicOrthocrossing
