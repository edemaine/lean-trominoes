/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCrossingRecordData
import LeanTrominoes.PeriodicOrthocrossingCarrierOrbitOwnership

/-! # Retained crossing records reconstructed from occurrence pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Translate a crossing record by an explicit numeric drawing period. -/
def crossingRecordPeriodTranslateAtPeriod
    (period : Nat) (record : CrossingRecord)
    (shift : Cell) : CrossingRecord where
  first := record.first
  firstTranslate := Cell.add record.firstTranslate shift
  second := record.second
  secondTranslate := Cell.add record.secondTranslate shift
  point := Cell.add record.point (Cell.scale (period : Int) shift)

/-- Reconstruct the complete retained translation block belonging to one
canonical occurrence pair. -/
def occurrencePairRetainedCrossingRecordBlockAtPeriod
    (period : Nat)
    (pair : (IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell)) : List CrossingRecord :=
  carrierCrossingRetentionShifts.map fun shift =>
    crossingRecordPeriodTranslateAtPeriod period
      (occurrencePairCrossingRecordAtPeriod period pair) shift

/-- Reconstruct retained crossing records from an arbitrary ordered accepted
occurrence-pair stream. -/
def occurrencePairRetainedCrossingRecordScanAtPeriod
    (period : Nat)
    (pairs : List ((IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell))) : List CrossingRecord :=
  pairs.flatMap
    (occurrencePairRetainedCrossingRecordBlockAtPeriod period)

end LeanTrominoes.PeriodicOrthocrossing
