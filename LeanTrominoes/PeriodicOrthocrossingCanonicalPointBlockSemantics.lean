/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalPointBlockMembership

/-! # Exact semantics of one canonical point block -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Scanning every fundamental point for one occurrence pair emits either
its unique computed oriented crossing or nothing. -/
theorem canonicalOrientedPointBlock_eq_singleton_if
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (pair : (IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell)) :
    canonicalOrientedPointBlock graph pair =
      if canonicalOrientedOccurrencePair graph pair then
        [orientedCrossingCandidate graph pair.1 pair.2]
      else [] := by
  cases accepted : canonicalOrientedOccurrencePair graph pair
  · simp only [Bool.false_eq]
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro record recordMember
    have data :=
      (mem_canonicalOrientedPointBlock_iff graph pair record).mp
        recordMember
    simp [accepted] at data
  · simp only [↓reduceIte]
    have permutation :
        (canonicalOrientedPointBlock graph pair).Perm
          [orientedCrossingCandidate graph pair.1 pair.2] := by
      apply (List.perm_ext_iff_of_nodup
        (canonicalOrientedPointBlock_nodup graph pair) (by simp)).mpr
      intro record
      rw [mem_canonicalOrientedPointBlock_iff]
      simp [accepted]
    simpa only [List.perm_singleton] using permutation

end LeanTrominoes.PeriodicOrthocrossing
