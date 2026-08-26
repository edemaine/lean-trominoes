/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalIndexSemantics
import Mathlib.Data.List.Nodup

/-! # Distinctness of global carrier-rank blocks -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankGlobal

theorem keyBlock_nodup (datums : List CarrierNodeRankDatum)
    (key : CarrierRankCompiledKey) :
    (keyBlock datums key).Nodup := by
  rw [keyBlock_eq_insertionSort]
  have zipNodup : datums.zipIdx.Nodup :=
    List.Nodup.of_map Prod.snd (List.nodup_zipIdx_map_snd datums)
  exact (List.perm_insertionSort
    (fun first second : CarrierNodeRankDatum × Nat =>
      StableListRanks.indexedCoordinate
          CarrierNodeRankDatum.orderCoordinate first ≤
        StableListRanks.indexedCoordinate
          CarrierNodeRankDatum.orderCoordinate second)
    (datums.zipIdx.filter fun entry => selectedKey key entry.1)).nodup_iff.mpr
      (zipNodup.filter _)

end CarrierRankGlobal
end LeanTrominoes.PeriodicOrthocrossing
