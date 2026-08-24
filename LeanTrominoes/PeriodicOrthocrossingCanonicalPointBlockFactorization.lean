/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalPointBlockSemantics

/-! # Point-block factorization of canonical crossings -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Two successive filters distribute through a flattened block stream. -/
private theorem filter_filter_flatMap
    {Index Output : Type}
    (indices : List Index) (blocks : Index → List Output)
    (first second : Output → Bool) :
    ((indices.flatMap blocks).filter first).filter second =
      indices.flatMap fun index =>
        ((blocks index).filter first).filter second := by
  induction indices with
  | nil => rfl
  | cons index indices induction =>
      simp [induction]

/-- The original point-grid definition of canonical oriented crossings is
the last-occurrence deduplication of its occurrence-pair point blocks. -/
theorem orientedCrossings_eq_pointBlock_dedup
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    orientedCrossings graph =
      ((neighborOccurrences graph).flatMap fun first =>
        (neighborOccurrences graph).flatMap fun second =>
          canonicalOrientedPointBlock graph (first, second)).dedup := by
  unfold orientedCrossings canonicalCrossings crossingCandidates
  rw [filter_filter_flatMap]
  congr 1
  apply List.flatMap_congr
  intro first _firstMember
  rw [filter_filter_flatMap]
  rfl

end LeanTrominoes.PeriodicOrthocrossing
