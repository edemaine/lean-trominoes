/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.IndexedConsecutivePairsIndexSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalBlockNodupSemantics

/-! # Same-key global-rank successors -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankGlobal

/-- Among presented indexed data with the same aggregate carrier key, a
global-rank successor is exactly an adjacent pair in their stable key block. -/
theorem rankAt_eq_succ_iff_mem_keyBlock_pairs
    (datums : List CarrierNodeRankDatum)
    (first second : CarrierNodeRankDatum × Nat)
    (firstMember : first ∈ datums.zipIdx)
    (secondMember : second ∈ datums.zipIdx)
    (sameKey : entryKey first = entryKey second) :
    rankAt datums second = rankAt datums first + 1 ↔
      (first, second) ∈ IndexedConsecutivePairs.pairs
        (keyBlock datums (entryKey first)) := by
  have firstBlockMember :
      first ∈ keyBlock datums (entryKey first) :=
    (mem_keyBlock_iff datums (entryKey first) first).mpr
      ⟨firstMember, rfl⟩
  have secondBlockMember :
      second ∈ keyBlock datums (entryKey first) :=
    (mem_keyBlock_iff datums (entryKey first) second).mpr
      ⟨secondMember, sameKey.symm⟩
  have rankEq :
      rankAt datums second = rankAt datums first + 1 ↔
        CarrierRankStableLower.stableRankAt datums second =
          CarrierRankStableLower.stableRankAt datums first + 1 := by
    unfold rankAt
    change CarrierRankCompiledKey.ofDatum first.1 =
      CarrierRankCompiledKey.ofDatum second.1 at sameKey
    rw [← sameKey]
    omega
  rw [rankEq]
  rw [stableRankAt_eq_idxOf_keyBlock datums first firstMember]
  rw [stableRankAt_eq_idxOf_keyBlock datums second secondMember]
  rw [← sameKey]
  simpa only [firstBlockMember, secondBlockMember, true_and] using
    (IndexedConsecutivePairs.mem_pairs_iff_idxOf_eq_succ
      (keyBlock datums (entryKey first))
      (keyBlock_nodup datums (entryKey first)) first second).symm

end CarrierRankGlobal
end LeanTrominoes.PeriodicOrthocrossing
