/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeCodeSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizationOffsetFieldData

/-! # Rank semantics of carrier normalization-offset fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierNormalizationOffsetField

@[simp] theorem rankValue_carrierNodeRankDatumAtPeriod
    (field : Field) (period : Nat) (node : CarrierNode) :
    rankValue field (carrierNodeRankDatumAtPeriod period node) =
      nodeValueAtPeriod field period node := by
  rfl

end CarrierNormalizationOffsetField
end LeanTrominoes.PeriodicOrthocrossing
