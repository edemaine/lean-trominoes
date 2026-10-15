/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Basic

/-! # Identifying two aligned mapped columns -/

namespace List

/-- Two columns presented as maps over the same keys remain aligned after
one column is read through a pointwise lookup. -/
theorem eq_map_lookup_of_aligned_maps
    {Key First Index : Type*}
    (keys : List Key) (firsts : List First) (indices : List Index)
    (first : Key → First) (index : Key → Index)
    (lookup : Index → First)
    (firstEq : firsts = keys.map first)
    (indicesEq : indices = keys.map index)
    (pointwise : ∀ key ∈ keys, first key = lookup (index key)) :
    firsts = indices.map lookup := by
  rw [firstEq, indicesEq, List.map_map]
  apply List.map_congr_left
  intro key keyMember
  exact pointwise key keyMember

end List
