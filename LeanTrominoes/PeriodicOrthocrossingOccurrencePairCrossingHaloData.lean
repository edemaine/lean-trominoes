/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierNormalizationData
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCrossingRecordData

/-! # Graph-free physical crossing-halo scans -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The horizontal-first physical crossing-halo test written using only a
numeric drawing period and an ordered pair of segment occurrences.  Unlike
the canonical crossing predicate, the intersection point may lie outside the
fundamental drawing square. -/
def orientedOccurrencePairInCrossingHaloAtPeriod
    (period : Nat)
    (pair : (IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell)) : Bool :=
  let first := occurrenceSegmentAtPeriod period pair.1
  let second := occurrenceSegmentAtPeriod period pair.2
  let point := orientedIntersectionPoint first second
  decide
    (PeriodicGridDrawing.SegmentOccurrenceKey pair.1.1 pair.1.2 ≠
        PeriodicGridDrawing.SegmentOccurrenceKey pair.2.1 pair.2.2 ∧
      first.IsHorizontal ∧ second.IsVertical ∧
      GridSegment.ProperlyCrossesAt first second point)

/-- Physical horizontal-first crossings in the exact occurrence-product
order, before periodic normalization identifies translated copies. -/
def occurrencePairCrossingHaloAtPeriod
    (period : Nat)
    (occurrences : List (IndexedGridSegment × Cell)) :
    List ((IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell)) :=
  (occurrences ×ˢ occurrences).filter
    (orientedOccurrencePairInCrossingHaloAtPeriod period)

/-- Normalize every physical crossing record and retain the last copy of each
canonical record.  This is the graph-free numeric presentation order used by
the final crossover family. -/
def occurrencePairCanonicalizedCrossingHaloAtPeriod
    (period : Nat)
    (occurrences : List (IndexedGridSegment × Cell)) : List CrossingRecord :=
  ((occurrencePairCrossingHaloAtPeriod period occurrences).map fun pair =>
    crossingRecordPeriodNormalizeAtPeriod period
      (occurrencePairCrossingRecordAtPeriod period pair)).dedup

end LeanTrominoes.PeriodicOrthocrossing
