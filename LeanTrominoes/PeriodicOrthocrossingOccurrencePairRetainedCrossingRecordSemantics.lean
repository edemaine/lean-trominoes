/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairRetainedCrossingRecordData
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCrossingRecordSemantics

/-! # Semantics of retained occurrence-pair crossing records -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Explicit-period record translation agrees with semantic graph translation
at the graph's exact drawing period. -/
theorem crossingRecordPeriodTranslateAtPeriod_drawingGridSize
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (record : CrossingRecord) (shift : Cell) :
    crossingRecordPeriodTranslateAtPeriod
        (drawingGridSize graph) record shift =
      record.periodTranslate graph shift := by
  simp [crossingRecordPeriodTranslateAtPeriod,
    CrossingRecord.periodTranslate,
    PeriodicGridDrawing.periodTranslation, drawing_gridSize]

/-- The reconstructed retained block is exactly the semantic translation
block of the occurrence pair's crossing candidate. -/
theorem occurrencePairRetainedCrossingRecordBlockAtPeriod_drawingGridSize
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (pair : (IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell)) :
    occurrencePairRetainedCrossingRecordBlockAtPeriod
        (drawingGridSize graph) pair =
      carrierCrossingRetentionShifts.map fun shift =>
        (orientedCrossingCandidate graph pair.1 pair.2).periodTranslate
          graph shift := by
  unfold occurrencePairRetainedCrossingRecordBlockAtPeriod
  apply List.map_congr_left
  intro shift _shiftMember
  rw [crossingRecordPeriodTranslateAtPeriod_drawingGridSize,
    occurrencePairCrossingRecordAtPeriod_drawingGridSize]

/-- Reconstructed retained crossing scans agree pointwise with semantic
crossing-candidate translation scans. -/
theorem occurrencePairRetainedCrossingRecordScanAtPeriod_drawingGridSize
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (pairs : List ((IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell))) :
    occurrencePairRetainedCrossingRecordScanAtPeriod
        (drawingGridSize graph) pairs =
      pairs.flatMap fun pair =>
        carrierCrossingRetentionShifts.map fun shift =>
          (orientedCrossingCandidate graph pair.1 pair.2).periodTranslate
            graph shift := by
  unfold occurrencePairRetainedCrossingRecordScanAtPeriod
  apply List.flatMap_congr
  intro pair _pairMember
  exact
    occurrencePairRetainedCrossingRecordBlockAtPeriod_drawingGridSize
      graph pair

end LeanTrominoes.PeriodicOrthocrossing
