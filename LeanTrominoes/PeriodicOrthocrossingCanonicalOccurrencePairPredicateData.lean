/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GridSegmentTranslationAxisSemantics
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

/-- An accepted canonical-oriented occurrence pair has a horizontal first
source segment and a vertical second source segment. -/
theorem axes_of_canonicalOrientedOccurrencePairAtPeriod
    (period : Nat)
    (pair : (IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell))
    (accepted : canonicalOrientedOccurrencePairAtPeriod period pair = true) :
    pair.1.1.segment.IsHorizontal ∧ pair.2.1.segment.IsVertical := by
  have conditions := of_decide_eq_true accepted
  rcases conditions with
    ⟨⟨_bounds, _different, proper⟩, firstHorizontal⟩
  have secondVertical :
      (occurrenceSegmentAtPeriod period pair.2).IsVertical := by
    rcases proper.2.2 with horizontalVertical | verticalHorizontal
    · exact horizontalVertical.2
    · exact False.elim
        (firstHorizontal.2 verticalHorizontal.1.1)
  constructor
  · simpa only [occurrenceSegmentAtPeriod,
      GridSegment.translate_isHorizontal_iff] using firstHorizontal
  · simpa only [occurrenceSegmentAtPeriod,
      GridSegment.translate_isVertical_iff] using secondVertical

end PeriodicOrthocrossing
end LeanTrominoes
