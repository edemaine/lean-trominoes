/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastOccurrenceBlockStarts
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyBlockStartCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyLastContributionSemantics

/-! # Semantics of per-occurrence carrier-key block starts -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeyBlockStarts

/-- Every aggregate key receives the start of its block in dedup-last order. -/
theorem starts_eq_lastOccurrenceBlockStarts
    (descriptors : List RouteDescriptor) :
    starts descriptors =
      LastOccurrenceBlockStarts.starts
        (CarrierRankCompiledKey.values descriptors) := by
  unfold starts CarrierRankKeyEqualityRows.semanticRows
  rw [CarrierRankKeyContributionStarts.starts,
    CarrierRankKeyLastContributions.contributions_eq_lastOccurrenceContributions]
  exact LastOccurrenceBlockStarts.lookups_equalityRows_contributionStarts
    (CarrierRankCompiledKey.values descriptors)

@[simp] theorem starts_length (descriptors : List RouteDescriptor) :
    (starts descriptors).length =
      (CarrierRankCompiledKey.values descriptors).length := by
  rw [starts_eq_lastOccurrenceBlockStarts]
  simp [LastOccurrenceBlockStarts.starts]

end CarrierRankKeyBlockStarts
end LeanTrominoes.PeriodicOrthocrossing
