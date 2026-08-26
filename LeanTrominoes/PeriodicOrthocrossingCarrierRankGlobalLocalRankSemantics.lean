/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalBlockSemantics
import LeanTrominoes.StableListIndexedLowerRankSemantics

/-! # Local indices inside global carrier-rank blocks -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankGlobal

/-- The stable same-key geometric rank is the exact local index of the
globally indexed datum in its aggregate-key block. -/
theorem stableRankAt_eq_idxOf_keyBlock
    (datums : List CarrierNodeRankDatum)
    (entry : CarrierNodeRankDatum × Nat)
    (member : entry ∈ datums.zipIdx) :
    CarrierRankStableLower.stableRankAt datums entry =
      @List.idxOf (CarrierNodeRankDatum × Nat) instBEqOfDecidableEq entry
        (keyBlock datums (entryKey entry)) := by
  have selectedEq :
      (fun other : CarrierNodeRankDatum =>
        decide (entry.1.key = other.key)) =
      selectedKey (entryKey entry) := by
    funext other
    simp [selectedKey, datumKey, entryKey, eq_comm]
  unfold CarrierRankStableLower.stableRankAt
  rw [selectedEq]
  simpa only [keyBlock] using
    StableListRanks.selectedIndexedLowerRank_eq_idxOf_rankEnumeration
      CarrierNodeRankDatum.orderCoordinate
      (selectedKey (entryKey entry)) datums entry member
      (by simp [selectedKey, datumKey, entryKey])

end CarrierRankGlobal
end LeanTrominoes.PeriodicOrthocrossing
