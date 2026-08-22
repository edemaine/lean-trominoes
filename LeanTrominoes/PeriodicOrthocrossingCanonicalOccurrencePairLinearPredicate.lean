/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalOccurrencePairPredicateData

/-! # Linear form of the canonical oriented crossing predicate -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Once the first segment is required to be horizontal, proper crossing at
the unique oriented intersection is exactly verticality of the second segment
plus two strict one-dimensional interval tests. -/
theorem properlyCrossesAt_orientedIntersectionPoint_iff
    (first second : GridSegment)
    (firstHorizontal : first.IsHorizontal) :
    GridSegment.ProperlyCrossesAt first second
        (orientedIntersectionPoint first second) ↔
      second.IsVertical ∧
        GridSegment.StrictlyBetween
          first.start.1 first.finish.1 second.start.1 ∧
        GridSegment.StrictlyBetween
          second.start.2 second.finish.2 first.start.2 := by
  constructor
  · rintro ⟨firstContains, secondContains, axes⟩
    have secondVertical : second.IsVertical := by
      rcases axes with axes | axes
      · exact axes.2
      · exact False.elim (firstHorizontal.2 axes.1.1)
    have firstBetween : GridSegment.StrictlyBetween
        first.start.1 first.finish.1 second.start.1 := by
      rcases firstContains with horizontal | vertical
      · exact horizontal.2.2
      · exact False.elim (firstHorizontal.2 vertical.1.1)
    have secondBetween : GridSegment.StrictlyBetween
        second.start.2 second.finish.2 first.start.2 := by
      rcases secondContains with horizontal | vertical
      · exact False.elim (secondVertical.2 horizontal.1.1)
      · exact vertical.2.2
    exact ⟨secondVertical, firstBetween, secondBetween⟩
  · rintro ⟨secondVertical, firstBetween, secondBetween⟩
    exact ⟨
      Or.inl ⟨firstHorizontal, rfl, firstBetween⟩,
      Or.inr ⟨secondVertical, rfl, secondBetween⟩,
      Or.inl ⟨firstHorizontal, secondVertical⟩⟩

/-- Quantifier-free linear conditions for one oriented neighboring occurrence
pair. -/
def canonicalOrientedOccurrencePairLinearConditionsAtPeriod
    (period : Nat)
    (pair : (IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell)) : Prop :=
  let first := occurrenceSegmentAtPeriod period pair.1
  let second := occurrenceSegmentAtPeriod period pair.2
  0 ≤ second.start.1 ∧ second.start.1 < period ∧
    0 ≤ first.start.2 ∧ first.start.2 < period ∧
    PeriodicGridDrawing.SegmentOccurrenceKey pair.1.1 pair.1.2 ≠
      PeriodicGridDrawing.SegmentOccurrenceKey pair.2.1 pair.2.2 ∧
    first.IsHorizontal ∧ second.IsVertical ∧
    GridSegment.StrictlyBetween
      first.start.1 first.finish.1 second.start.1 ∧
    GridSegment.StrictlyBetween
      second.start.2 second.finish.2 first.start.2

instance canonicalOrientedOccurrencePairLinearConditionsAtPeriodDecidable
    (period : Nat)
    (pair : (IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell)) :
    Decidable
      (canonicalOrientedOccurrencePairLinearConditionsAtPeriod
        period pair) := by
  unfold canonicalOrientedOccurrencePairLinearConditionsAtPeriod
  infer_instance

/-- Boolean form consumed by the later fixed arithmetic evaluator. -/
def canonicalOrientedOccurrencePairLinearAtPeriod
    (period : Nat)
    (pair : (IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell)) : Bool :=
  decide (canonicalOrientedOccurrencePairLinearConditionsAtPeriod
    period pair)

/-- The graph-free canonical crossing predicate is exactly its linearized
oriented form. -/
theorem canonicalOrientedOccurrencePairAtPeriod_eq_linear
    (period : Nat)
    (pair : (IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell)) :
    canonicalOrientedOccurrencePairAtPeriod period pair =
      canonicalOrientedOccurrencePairLinearAtPeriod period pair := by
  unfold canonicalOrientedOccurrencePairAtPeriod
    canonicalOrientedOccurrencePairLinearAtPeriod
    canonicalOrientedOccurrencePairLinearConditionsAtPeriod
  let first := occurrenceSegmentAtPeriod period pair.1
  let second := occurrenceSegmentAtPeriod period pair.2
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
  change
    ((((0 ≤ second.start.1 ∧ second.start.1 < period ∧
          0 ≤ first.start.2 ∧ first.start.2 < period) ∧
        PeriodicGridDrawing.SegmentOccurrenceKey pair.1.1 pair.1.2 ≠
          PeriodicGridDrawing.SegmentOccurrenceKey pair.2.1 pair.2.2 ∧
        GridSegment.ProperlyCrossesAt first second
          (orientedIntersectionPoint first second)) ∧
      first.IsHorizontal) ↔ _)
  constructor
  · rintro ⟨⟨bounds, different, proper⟩, horizontal⟩
    have linear :=
      (properlyCrossesAt_orientedIntersectionPoint_iff
        first second horizontal).mp proper
    exact ⟨bounds.1, bounds.2.1, bounds.2.2.1, bounds.2.2.2,
      different, horizontal, linear.1, linear.2.1, linear.2.2⟩
  · rintro ⟨firstX, firstXUpper, firstY, firstYUpper,
      different, horizontal, vertical, horizontalBetween,
      verticalBetween⟩
    have proper :=
      (properlyCrossesAt_orientedIntersectionPoint_iff
        first second horizontal).mpr
        ⟨vertical, horizontalBetween, verticalBetween⟩
    exact ⟨⟨⟨firstX, firstXUpper, firstY, firstYUpper⟩,
      different, proper⟩, horizontal⟩

end PeriodicOrthocrossing
end LeanTrominoes
