/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalizedCrossingHalo
import LeanTrominoes.PeriodicOrthocrossingCanonicalOccurrencePairs
import LeanTrominoes.PeriodicOrthocrossingCanonicalPairScanNodup
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierNormalizationSemantics
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCrossingHaloData
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCrossingRecordSemantics

/-! # Semantics of graph-free physical crossing-halo scans -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- At the drawing's numeric period, the graph-free predicate is exactly the
physical crossing-halo predicate on the record reconstructed from the same
occurrence pair. -/
@[simp] theorem orientedOccurrencePairInCrossingHaloAtPeriod_drawingGridSize
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (pair : (IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell)) :
    orientedOccurrencePairInCrossingHaloAtPeriod
        (drawingGridSize graph) pair =
      decide ((orientedCrossingCandidate graph pair.1 pair.2).IsInCrossingHalo
        graph) := by
  simp [orientedOccurrencePairInCrossingHaloAtPeriod,
    CrossingRecord.IsInCrossingHalo, orientedCrossingCandidate,
    occurrenceSegmentAtPeriod, CrossingRecord.firstSegment,
    CrossingRecord.secondSegment, PeriodicGridDrawing.periodTranslation,
    drawing_gridSize]

/-- Mapping physical graph-free occurrence pairs to crossing records recovers
the exact physical halo order. -/
theorem occurrencePairCrossingHaloAtPeriod_map_record_eq
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    (occurrencePairCrossingHaloAtPeriod
        (drawingGridSize graph) (neighborOccurrences graph)).map
        (occurrencePairCrossingRecordAtPeriod
          (drawingGridSize graph)) =
      orientedCrossingHalo graph := by
  unfold occurrencePairCrossingHaloAtPeriod orientedCrossingHalo
  rw [List.dedup_eq_self.mpr
    ((crossingHaloCandidates_nodup graph).filter _)]
  rw [crossingHaloCandidates_eq_map_occurrenceProduct]
  rw [List.filter_map]
  apply List.map_congr_left
  intro pair pairMember
  rw [occurrencePairCrossingRecordAtPeriod_drawingGridSize]

/-- The graph-free normalize-then-deduplicate scan is exactly the semantic
`canonicalizedCrossingHalo`, including its last-occurrence presentation
order. -/
theorem occurrencePairCanonicalizedCrossingHaloAtPeriod_eq
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    occurrencePairCanonicalizedCrossingHaloAtPeriod
        (drawingGridSize graph) (neighborOccurrences graph) =
      canonicalizedCrossingHalo graph := by
  unfold occurrencePairCanonicalizedCrossingHaloAtPeriod
    canonicalizedCrossingHalo
  rw [← occurrencePairCrossingHaloAtPeriod_map_record_eq graph,
    List.map_map]
  apply congrArg List.dedup
  apply List.map_congr_left
  intro pair pairMember
  simp only [Function.comp_apply]
  rw [crossingRecordPeriodNormalizeAtPeriod_drawingGridSize]

end LeanTrominoes.PeriodicOrthocrossing
