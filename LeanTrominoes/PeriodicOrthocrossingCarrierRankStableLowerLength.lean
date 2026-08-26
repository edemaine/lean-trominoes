/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankStableLowerData
import LeanTrominoes.UnaryAlignedAddSemantics

/-! # Length of compiled stable carrier ranks -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankStableLower

@[simp] theorem ranks_length (descriptors : List RouteDescriptor) :
    (ranks descriptors).length = side descriptors := by
  have lengthEq := UnaryAlignedAddMachine.sums_length
    (additionInput descriptors).valid
  simpa only [ranks, additionInput, lowerCounts_length] using lengthEq

end CarrierRankStableLower
end LeanTrominoes.PeriodicOrthocrossing
