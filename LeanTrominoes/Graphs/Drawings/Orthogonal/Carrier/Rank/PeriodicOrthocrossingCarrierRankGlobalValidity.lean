/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.Carrier.Rank.PeriodicOrthocrossingCarrierRankKeyBlockStartSemantics
import LeanTrominoes.Graphs.Drawings.Orthogonal.Carrier.Rank.PeriodicOrthocrossingCarrierRankStableLowerLength
import LeanTrominoes.Computation.Encoding.Unary.UnaryAlignedAddValidity

/-! # Alignment validity for global carrier ranks -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankGlobalValidity

theorem lengths_eq (descriptors : List RouteDescriptor) :
    (CarrierRankKeyBlockStarts.starts descriptors).length =
      (CarrierRankStableLower.ranks descriptors).length := by
  rw [CarrierRankKeyBlockStarts.starts_length,
    CarrierRankStableLower.ranks_length,
    CarrierRankCompiledKey.values_length]
  rfl

opaque valid (descriptors : List RouteDescriptor) :
    UnaryAlignedAddMachine.Valid
      (CarrierRankKeyBlockStarts.starts descriptors)
      (CarrierRankStableLower.ranks descriptors) :=
  UnaryAlignedAddMachine.Valid.of_length_eq (lengths_eq descriptors)

end CarrierRankGlobalValidity
end LeanTrominoes.PeriodicOrthocrossing
