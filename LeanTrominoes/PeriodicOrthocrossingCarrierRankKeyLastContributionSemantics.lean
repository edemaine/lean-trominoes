/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastOccurrenceContributions
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyLastContribution

/-! # Semantics of last-occurrence carrier-key contributions -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeyLastContributions

theorem contributions_eq_lastOccurrenceContributions
    (descriptors : List RouteDescriptor) :
    contributions descriptors =
      LastOccurrenceContributions.contributions
        (CarrierRankCompiledKey.values descriptors) := by
  unfold contributions
  rw [CarrierRankKeyOccurrenceRanks.ranks_eq_stableRanks,
    CarrierRankKeyGroupSizes.sizes_eq_keyCounts]
  exact LastOccurrenceContributions.selectedValues_stableRanks
    (CarrierRankCompiledKey.values descriptors)

end CarrierRankKeyLastContributions
end LeanTrominoes.PeriodicOrthocrossing
