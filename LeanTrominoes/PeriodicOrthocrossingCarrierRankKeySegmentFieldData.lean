/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyFieldData

/-! # Selected carrier-key segment field -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeySegmentField

/-- Segment-index values at compact carrier-node representatives. -/
def values (descriptors : List RouteDescriptor) : List Nat :=
  CarrierRankKeyField.values .segment descriptors

end CarrierRankKeySegmentField
end LeanTrominoes.PeriodicOrthocrossing
