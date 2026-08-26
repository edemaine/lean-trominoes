/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalEnumerationData
import LeanTrominoes.StableListRankEnumerationSemantics
import LeanTrominoes.StrictListRankEnumerationNodupSemantics

/-! # Semantics of per-key global carrier-rank blocks -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankGlobal

private theorem keyBlock_coordinate_nodup
    (datums : List CarrierNodeRankDatum)
    (key : CarrierRankCompiledKey) :
    ((datums.zipIdx.filter fun entry => selectedKey key entry.1).map
      (StableListRanks.indexedCoordinate
        CarrierNodeRankDatum.orderCoordinate)).Nodup := by
  exact (StableListRanks.indexedCoordinate_zipIdx_nodup
    CarrierNodeRankDatum.orderCoordinate datums).sublist
      (List.filter_sublist.map
        (StableListRanks.indexedCoordinate
          CarrierNodeRankDatum.orderCoordinate))

theorem keyBlock_eq_insertionSort
    (datums : List CarrierNodeRankDatum)
    (key : CarrierRankCompiledKey) :
    keyBlock datums key =
      (datums.zipIdx.filter fun entry => selectedKey key entry.1).insertionSort
        fun first second =>
          StableListRanks.indexedCoordinate
              CarrierNodeRankDatum.orderCoordinate first ≤
            StableListRanks.indexedCoordinate
              CarrierNodeRankDatum.orderCoordinate second := by
  unfold keyBlock
  exact
    StrictListRanks.valuesByLowerRank_eq_insertionSort_of_coordinate_nodup
      (StableListRanks.indexedCoordinate
        CarrierNodeRankDatum.orderCoordinate)
      (datums.zipIdx.filter fun entry => selectedKey key entry.1)
      (keyBlock_coordinate_nodup datums key)

@[simp] theorem mem_keyBlock_iff
    (datums : List CarrierNodeRankDatum)
    (key : CarrierRankCompiledKey)
    (entry : CarrierNodeRankDatum × Nat) :
    entry ∈ keyBlock datums key ↔
      entry ∈ datums.zipIdx ∧ entryKey entry = key := by
  rw [keyBlock_eq_insertionSort]
  simp [selectedKey, datumKey, entryKey]

private theorem filter_zipIdx_length_eq_filter
    {Value : Type*} (values : List Value) (start : Nat)
    (selected : Value → Bool) :
    ((values.zipIdx start).filter fun entry => selected entry.1).length =
      (values.filter selected).length := by
  induction values generalizing start with
  | nil => rfl
  | cons value values induction =>
      by_cases active : selected value
      · simp [List.zipIdx_cons, active, induction (start + 1)]
      · simp [List.zipIdx_cons, active, induction (start + 1)]

private theorem filter_length_eq_count_map
    (datums : List CarrierNodeRankDatum)
    (key : CarrierRankCompiledKey) :
    (datums.filter fun datum =>
      selectedKey key datum).length =
        (datums.map CarrierRankCompiledKey.ofDatum).count key := by
  induction datums with
  | nil => rfl
  | cons datum datums induction =>
      by_cases active : selectedKey key datum
      · have same : CarrierRankCompiledKey.ofDatum datum = key := by
          simpa [selectedKey, datumKey] using active
        simp [active, same, induction]
      · have same : ¬CarrierRankCompiledKey.ofDatum datum = key := by
          simpa [selectedKey, datumKey] using active
        simp [active, same, induction]

@[simp] theorem keyBlock_length
    (datums : List CarrierNodeRankDatum)
    (key : CarrierRankCompiledKey) :
    (keyBlock datums key).length =
      (datums.map CarrierRankCompiledKey.ofDatum).count key := by
  rw [keyBlock_eq_insertionSort, List.length_insertionSort]
  rw [filter_zipIdx_length_eq_filter datums 0 (selectedKey key)]
  exact filter_length_eq_count_map datums key

theorem entryKey_eq_of_mem_keyBlock
    (datums : List CarrierNodeRankDatum)
    (key : CarrierRankCompiledKey)
    (entry : CarrierNodeRankDatum × Nat)
    (member : entry ∈ keyBlock datums key) :
    entryKey entry = key :=
  (mem_keyBlock_iff datums key entry).mp member |>.2

end CarrierRankGlobal
end LeanTrominoes.PeriodicOrthocrossing
