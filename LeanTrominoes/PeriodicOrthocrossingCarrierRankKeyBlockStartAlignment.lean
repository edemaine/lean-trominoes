/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyContributionStartLength

/-! # Row/value alignment for carrier-key block starts -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeyBlockStartAlignment

theorem semanticRows_forall_starts_length
    (descriptors : List RouteDescriptor) :
    (CarrierRankKeyEqualityRows.semanticRows descriptors).Forall fun row =>
      row.length =
        (CarrierRankKeyContributionStarts.starts descriptors).length := by
  have startsLength :=
    CarrierRankKeyContributionStarts.starts_length_eq_key_side descriptors
  rw [CarrierRankKeyEqualityRows.side_eq_compiledKeys_length] at startsLength
  unfold CarrierRankKeyEqualityRows.semanticRows
  rw [List.forall_iff_forall_mem]
  intro row rowMem
  rcases List.mem_map.mp rowMem with ⟨key, _keyMem, rfl⟩
  simp [StableOccurrenceRanks.equalityRow, startsLength]

end CarrierRankKeyBlockStartAlignment
end LeanTrominoes.PeriodicOrthocrossing
