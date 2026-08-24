/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalOccurrencePairPredicateData

/-! # Crossing records reconstructed from occurrence pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Reconstruct the canonical crossing record of an ordered occurrence pair
using only an explicit numeric drawing period. -/
def occurrencePairCrossingRecordAtPeriod
    (period : Nat)
    (pair : (IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell)) : CrossingRecord where
  first := pair.1.1
  firstTranslate := pair.1.2
  second := pair.2.1
  secondTranslate := pair.2.2
  point := orientedIntersectionPoint
    (occurrenceSegmentAtPeriod period pair.1)
    (occurrenceSegmentAtPeriod period pair.2)

end LeanTrominoes.PeriodicOrthocrossing
