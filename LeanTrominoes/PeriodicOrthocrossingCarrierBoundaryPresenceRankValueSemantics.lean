/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPresenceRankValueData
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeCodeSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumLookupData

/-! # Boundary-presence rank values of encoded carrier nodes -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierBoundaryPresenceField

@[simp] theorem rankValue_carrierNodeRankDatumAtPeriod
    (period : Nat) (node : CarrierNode) :
    rankValue (carrierNodeRankDatumAtPeriod period node) = nodeValue node := by
  cases node <;> rfl

@[simp] theorem fieldValueAtPeriod_rankValue_map_code
    (period : Nat) (node : Option CarrierNode) :
    CarrierRankDatumLookup.fieldValueAtPeriod period rankValue
        (node.map CarrierNode.code) =
      optionalNodeValue node := by
  cases node with
  | none => rfl
  | some node =>
      simp [CarrierRankDatumLookup.fieldValueAtPeriod, optionalNodeValue]

end CarrierBoundaryPresenceField
end LeanTrominoes.PeriodicOrthocrossing
