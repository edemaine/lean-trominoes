/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyContributionStartCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyEqualityRowSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyLastContributionSemantics

/-! # Length of carrier-key contribution starts -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeyContributionStarts

theorem starts_length_eq_key_side (descriptors : List RouteDescriptor) :
    (starts descriptors).length =
      CarrierRankKeyEqualityRows.side descriptors := by
  unfold starts
  rw [PrefixSums.starts_length,
    CarrierRankKeyLastContributions.contributions_eq_lastOccurrenceContributions,
    LastOccurrenceContributions.contributions_length,
    CarrierRankKeyEqualityRows.side_eq_compiledKeys_length]

end CarrierRankKeyContributionStarts
end LeanTrominoes.PeriodicOrthocrossing
