/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalOccurrencePairs

/-! # Graph-free canonical occurrence-pair predicate -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Translate one indexed segment occurrence using only the numeric drawing
period. -/
def occurrenceSegmentAtPeriod
    (period : Nat) (occurrence : IndexedGridSegment × Cell) : GridSegment :=
  occurrence.1.segment.translate
    (Cell.scale (period : Int) occurrence.2)

/-- The canonical horizontal-first crossing test written using only a numeric
period and an ordered pair of neighboring indexed segment occurrences. -/
def canonicalOrientedOccurrencePairAtPeriod
    (period : Nat)
    (pair : (IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell)) : Bool :=
  let first := occurrenceSegmentAtPeriod period pair.1
  let second := occurrenceSegmentAtPeriod period pair.2
  let point := orientedIntersectionPoint first second
  decide
    (((0 ≤ point.1 ∧ point.1 < period ∧
        0 ≤ point.2 ∧ point.2 < period) ∧
      PeriodicGridDrawing.SegmentOccurrenceKey pair.1.1 pair.1.2 ≠
          PeriodicGridDrawing.SegmentOccurrenceKey pair.2.1 pair.2.2 ∧
        GridSegment.ProperlyCrossesAt first second point) ∧
      first.IsHorizontal)

end PeriodicOrthocrossing
end LeanTrominoes
