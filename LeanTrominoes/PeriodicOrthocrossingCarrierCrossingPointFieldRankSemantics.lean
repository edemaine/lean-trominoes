/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingPointFieldData
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeCodeSemantics

/-! # Rank semantics of crossing-point fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierCrossingPointField

@[simp] theorem rankValue_carrierNodeRankDatumAtPeriod
    (field : Field) (period : Nat) (node : CarrierNode) :
    rankValue field (carrierNodeRankDatumAtPeriod period node) =
      nodeValue field node := by
  cases node with
  | terminal terminal => rfl
  | boundary boundary =>
      cases field <;>
        simp [rankValue, nodeValue, pointValue,
          horizontal, keepPositive, carrierNodeRankDatumAtPeriod,
          CrossingRecord.code]

end CarrierCrossingPointField
end LeanTrominoes.PeriodicOrthocrossing
