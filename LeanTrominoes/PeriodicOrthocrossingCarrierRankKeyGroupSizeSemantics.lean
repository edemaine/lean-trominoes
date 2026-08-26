/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastRepresentativeEqualityRowCountsSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyEqualityRowSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyGroupSizeCompiler

/-! # Semantics of compiled carrier-key multiplicities -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeyGroupSizes

/-- Every full row count is the multiplicity of its aggregate key. -/
theorem sizes_eq_keyCounts (descriptors : List RouteDescriptor) :
    sizes descriptors =
      (CarrierRankCompiledKey.values descriptors).map fun key =>
        (CarrierRankCompiledKey.values descriptors).count key := by
  unfold sizes DelimitedBinaryWordTrueCounts.counts
  rw [CarrierRankKeyEqualityRows.rows_words]
  unfold CarrierRankKeyEqualityRows.semanticRows
  rw [List.map_map]
  apply List.map_congr_left
  intro key _keyMember
  exact LastRepresentativeEqualityRows.countTrue_equalityRow
    (CarrierRankCompiledKey.values descriptors) key

end CarrierRankKeyGroupSizes
end LeanTrominoes.PeriodicOrthocrossing
