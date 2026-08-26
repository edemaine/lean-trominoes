/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyGroupSizeSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyOccurrenceRankSemantics
import LeanTrominoes.StableOccurrenceRanksBounds

/-! # Validity of compiled carrier-key occurrence ranks -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeyRankValidity

/-- Every compiled stable occurrence rank is strictly below the full
multiplicity of its aggregate carrier key. -/
opaque valid (descriptors : List RouteDescriptor) :
    UnarySuccessorEqualityFilterMachine.Valid
      (CarrierRankKeyOccurrenceRanks.ranks descriptors)
      (CarrierRankKeyGroupSizes.sizes descriptors) := by
  rw [CarrierRankKeyOccurrenceRanks.ranks_eq_stableRanks,
    CarrierRankKeyGroupSizes.sizes_eq_keyCounts]
  exact StableOccurrenceRanks.ranks_valid
    (CarrierRankCompiledKey.values descriptors)

end CarrierRankKeyRankValidity
end LeanTrominoes.PeriodicOrthocrossing
