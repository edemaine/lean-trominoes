/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalIndexSemantics

/-! # Membership in global carrier-rank enumeration -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankGlobal

@[simp] theorem mem_enumeration_iff
    (datums : List CarrierNodeRankDatum)
    (entry : CarrierNodeRankDatum × Nat) :
    entry ∈ enumeration datums ↔ entry ∈ datums.zipIdx := by
  constructor
  · intro enumerationMember
    rcases List.mem_flatMap.mp enumerationMember with
      ⟨key, _keyMember, blockMember⟩
    exact (mem_keyBlock_iff datums key entry).mp blockMember |>.1
  · intro presentationMember
    apply List.mem_flatMap.mpr
    refine ⟨entryKey entry, ?_, ?_⟩
    · apply List.mem_dedup.mpr
      simpa [entryKey, datumKey] using
        (List.mem_map.mpr ⟨entry.1,
          List.fst_mem_of_mem_zipIdx presentationMember, rfl⟩ :
          CarrierRankCompiledKey.ofDatum entry.1 ∈
            datums.map CarrierRankCompiledKey.ofDatum)
    · exact (mem_keyBlock_iff datums (entryKey entry) entry).mpr
        ⟨presentationMember, rfl⟩

end CarrierRankGlobal
end LeanTrominoes.PeriodicOrthocrossing
