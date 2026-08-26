/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyEqualityRowSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyOccurrenceRankCompiler

/-! # Semantics of stable compiled carrier-key occurrence ranks -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeyOccurrenceRanks

/-- Prefix-true counting computes each aggregate key's stable occurrence
rank on every descriptor stream. -/
theorem ranks_eq_stableRanks (descriptors : List RouteDescriptor) :
    ranks descriptors =
      StableOccurrenceRanks.ranks
        (CarrierRankCompiledKey.values descriptors) := by
  unfold ranks DelimitedBinaryWordPrefixTrueCounts.counts
    StableOccurrenceRanks.ranks
  rw [CarrierRankKeyEqualityRows.rows_words]
  exact StableOccurrenceRanks.trueCountsAux_equalityRows
    (CarrierRankCompiledKey.values descriptors)
    (CarrierRankCompiledKey.values descriptors) 0

end CarrierRankKeyOccurrenceRanks
end LeanTrominoes.PeriodicOrthocrossing
