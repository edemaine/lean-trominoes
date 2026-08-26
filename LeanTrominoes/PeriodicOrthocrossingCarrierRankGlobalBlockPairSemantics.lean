/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.IndexedConsecutivePairsMapSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalBlockPairData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalBlockProjectionSemantics

/-! # Semantics of retained pairs inside global carrier-rank blocks -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankGlobal

/-- Adjacent indexed entries in a global key block project to the established
stable adjacent datum pairs for that semantic carrier. -/
theorem keyBlockDatumPairs_eq
    (datums : List CarrierNodeRankDatum) (datumsNodup : datums.Nodup)
    (key : Nat × Nat × Cell) :
    keyBlockDatumPairs datums key =
      IndexedConsecutivePairs.pairs
        (retainedCarrierRankDatumsByLowerRank datums key) := by
  unfold keyBlockDatumPairs
  rw [← IndexedConsecutivePairs.pairs_map]
  rw [keyBlock_map_fst_eq_retainedCarrierRankDatumsByLowerRank
    datums datumsNodup key]

/-- The complete filtered bit scan of one global key block is exactly the
previously established datum-only retained carrier scan. -/
theorem keyBlockBits_eq_retainedCarrierRankDatumBits
    (datums : List CarrierNodeRankDatum) (datumsNodup : datums.Nodup)
    (key : Nat × Nat × Cell) :
    keyBlockBits datums key = retainedCarrierRankDatumBits datums key := by
  unfold keyBlockBits retainedCarrierRankDatumBits
  rw [keyBlockDatumPairs_eq datums datumsNodup key]

end CarrierRankGlobal
end LeanTrominoes.PeriodicOrthocrossing
