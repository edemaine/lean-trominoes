/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingFundamentalPointNodup

/-! # Duplicate freedom of one canonical point block -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- An occurrence pair and its resulting record retain the explicit point
injectively. -/
theorem occurrencePairCrossingAtPoint_injective
    (pair : (IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell)) :
    Function.Injective (occurrencePairCrossingAtPoint pair) := by
  intro first second equal
  exact congrArg CrossingRecord.point equal

/-- Filtering one injective fundamental-point block preserves duplicate
freedom. -/
theorem canonicalOrientedPointBlock_nodup
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (pair : (IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell)) :
    (canonicalOrientedPointBlock graph pair).Nodup := by
  unfold canonicalOrientedPointBlock
  exact (((fundamentalPoints_nodup graph).map
    (occurrencePairCrossingAtPoint_injective pair)).filter _).filter _

end LeanTrominoes.PeriodicOrthocrossing
