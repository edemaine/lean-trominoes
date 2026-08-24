/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalOccurrencePairSingletonScanData
import LeanTrominoes.ListNestedProductFlatMap

/-! # Replacement of canonical point blocks by singleton blocks -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Replacing every original point-grid block by its proved singleton form
turns the nested canonical scan into the direct occurrence-pair scan. -/
theorem canonicalPointBlockNestedScan_eq_singletonScan
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    (neighborOccurrences graph).flatMap (fun first =>
        (neighborOccurrences graph).flatMap fun second =>
          canonicalOrientedPointBlock graph (first, second)) =
      canonicalOrientedOccurrencePairSingletonScan graph := by
  rw [nested_flatMap_eq_product_flatMap]
  unfold canonicalOrientedOccurrencePairSingletonScan
    canonicalOrientedOccurrencePairSingletonBlock
  apply List.flatMap_congr
  intro pair _pairMember
  exact canonicalOrientedPointBlock_eq_singleton_if graph pair

end LeanTrominoes.PeriodicOrthocrossing
