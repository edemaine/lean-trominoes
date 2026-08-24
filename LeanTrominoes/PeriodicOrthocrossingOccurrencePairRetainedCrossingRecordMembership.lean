/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairRetainedCrossingRecordData

/-! # Membership in retained occurrence-pair crossing-record scans -/

namespace LeanTrominoes.PeriodicOrthocrossing

theorem mem_occurrencePairRetainedCrossingRecordScanAtPeriod_iff
    (period : Nat)
    (pairs : List ((IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell)))
    (record : CrossingRecord) :
    record ∈ occurrencePairRetainedCrossingRecordScanAtPeriod
        period pairs ↔
      ∃ pair ∈ pairs, ∃ shift ∈ carrierCrossingRetentionShifts,
        crossingRecordPeriodTranslateAtPeriod period
          (occurrencePairCrossingRecordAtPeriod period pair) shift = record := by
  simp [occurrencePairRetainedCrossingRecordScanAtPeriod,
    occurrencePairRetainedCrossingRecordBlockAtPeriod]

end LeanTrominoes.PeriodicOrthocrossing
