/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Dedup

/-! # Stable deduplication governed by a final covering block -/

namespace List

/-- If every earlier block is contained in a duplicate-free final block,
stable last-representative deduplication retains exactly that final block. -/
theorem dedup_flatMap_append_singleton_eq_final
    {Index Value : Type*} [DecidableEq Value]
    (indices : List Index) (final : Index)
    (block : Index → List Value)
    (covered : ∀ index ∈ indices, block index ⊆ block final)
    (finalNodup : (block final).Nodup) :
    ((indices ++ [final]).flatMap block).dedup = block final := by
  rw [List.flatMap_append, List.flatMap_singleton]
  have prefixSubset : indices.flatMap block ⊆ block final := by
    intro value valueMember
    rcases List.mem_flatMap.mp valueMember with
      ⟨index, indexMember, valueMember⟩
    exact covered index indexMember valueMember
  rw [prefixSubset.dedup_append_right,
    List.dedup_eq_self.mpr finalNodup]

end List
