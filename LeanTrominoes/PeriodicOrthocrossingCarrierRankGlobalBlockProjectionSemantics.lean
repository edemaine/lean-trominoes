/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumScanData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalEnumerationData
import LeanTrominoes.StableListSelectedRankEnumerationSemantics

/-! # Projection of global carrier-rank blocks -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankGlobal

/-- For a duplicate-free datum presentation, forgetting the retained global
indices in one aggregate-key block recovers the established stable datum
enumeration for that semantic carrier key. -/
theorem keyBlock_map_fst_eq_retainedCarrierRankDatumsByLowerRank
    (datums : List CarrierNodeRankDatum) (datumsNodup : datums.Nodup)
    (key : Nat × Nat × Cell) :
    (keyBlock datums (CarrierRankCompiledKey.ofKey key)).map Prod.fst =
      retainedCarrierRankDatumsByLowerRank datums key := by
  unfold keyBlock retainedCarrierRankDatumsByLowerRank
  rw [StableListRanks.selectedIndexedValuesByLowerRank_map_fst]
  unfold retainedCarrierRankDatumCandidates
  rw [List.dedup_eq_self.mpr datumsNodup]
  apply congrArg (StableListRanks.valuesByStableLowerRank
    CarrierNodeRankDatum.orderCoordinate)
  apply List.filter_congr
  intro datum _datumMember
  simp [selectedKey, datumKey, CarrierRankCompiledKey.ofDatum]

end CarrierRankGlobal
end LeanTrominoes.PeriodicOrthocrossing
