/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeCodeSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierOwnershipShiftFieldData

/-! # Rank semantics of carrier ownership-shift fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierOwnershipShiftField

@[simp] theorem rankValue_carrierNodeRankDatumAtPeriod
    (field : Field) (period : Nat) (node : CarrierNode) :
    rankValue field (carrierNodeRankDatumAtPeriod period node) =
      nodeValueAtPeriod field period node := by
  cases node <;> rfl

end CarrierOwnershipShiftField
end LeanTrominoes.PeriodicOrthocrossing
