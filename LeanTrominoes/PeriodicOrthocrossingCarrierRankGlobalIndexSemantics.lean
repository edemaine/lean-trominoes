/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GroupedListIndex
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalLocalRankSemantics

/-! # Exact indices of global carrier ranks -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankGlobal

/-- A presented indexed datum's semantic global rank is its exact index in
the dedup-last-key-major, stable-coordinate enumeration. -/
theorem rankAt_eq_idxOf_enumeration
    (datums : List CarrierNodeRankDatum)
    (entry : CarrierNodeRankDatum × Nat)
    (member : entry ∈ datums.zipIdx) :
    rankAt datums entry =
      @List.idxOf (CarrierNodeRankDatum × Nat) instBEqOfDecidableEq entry
        (enumeration datums) := by
  let keys := (datums.map CarrierRankCompiledKey.ofDatum).dedup
  have keyMember : entryKey entry ∈ keys := by
    apply List.mem_dedup.mpr
    simpa [keys, entryKey, datumKey] using
      (List.mem_map.mpr ⟨entry.1,
        List.fst_mem_of_mem_zipIdx member, rfl⟩ :
        CarrierRankCompiledKey.ofDatum entry.1 ∈
          datums.map CarrierRankCompiledKey.ofDatum)
  have blockMember : entry ∈ keyBlock datums (entryKey entry) :=
    (mem_keyBlock_iff datums (entryKey entry) entry).mpr ⟨member, rfl⟩
  have grouped :=
    GroupedListIndex.idxOf_flatMap_eq_prefix_sum_add_local
      keys (keyBlock datums) entryKey (entryKey entry) entry
      (fun key value valueMember =>
        entryKey_eq_of_mem_keyBlock datums key value valueMember)
      rfl keyMember blockMember
  have rankEq :
      rankAt datums entry =
        (((keys.take
          (@List.idxOf CarrierRankCompiledKey instBEqOfDecidableEq
            (entryKey entry) keys)).map fun key =>
              (keyBlock datums key).length).sum) +
          @List.idxOf (CarrierNodeRankDatum × Nat) instBEqOfDecidableEq
            entry (keyBlock datums (entryKey entry)) := by
    unfold rankAt LastOccurrenceBlockStarts.blockStart
      LastOccurrenceBlockStarts.blockStartAux
    rw [stableRankAt_eq_idxOf_keyBlock datums entry member]
    simp [keys, entryKey, datumKey, keyBlock_length]
  calc
    rankAt datums entry =
        (((keys.take
          (@List.idxOf CarrierRankCompiledKey instBEqOfDecidableEq
            (entryKey entry) keys)).map fun key =>
              (keyBlock datums key).length).sum) +
          @List.idxOf (CarrierNodeRankDatum × Nat) instBEqOfDecidableEq
            entry (keyBlock datums (entryKey entry)) := rankEq
    _ = @List.idxOf (CarrierNodeRankDatum × Nat) instBEqOfDecidableEq
          entry (enumeration datums) := by
      simpa [enumeration, keys] using grouped.symm

end CarrierRankGlobal
end LeanTrominoes.PeriodicOrthocrossing
