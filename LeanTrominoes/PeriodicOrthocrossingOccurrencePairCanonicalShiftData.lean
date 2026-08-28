/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCrossingHaloData
import LeanTrominoes.PeriodicOrthocrossingRetainedCompactAtomWord

/-! # Fixed common-shift candidates for physical crossing pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Subtract one common lattice shift from both occurrences of an ordered
pair.  A physical halo crossing becomes canonical when the subtracted shift
is the quotient containing its crossing point. -/
def occurrencePairSubtractShift
    (pair : (IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell))
    (shift : Cell) :
    (IndexedGridSegment × Cell) × (IndexedGridSegment × Cell) :=
  ((pair.1.1, Cell.sub pair.1.2 shift),
    (pair.2.1, Cell.sub pair.2.2 shift))

/-- The optional canonical occurrence pair selected by one proposed common
shift. -/
def occurrencePairCanonicalShiftCandidateAtPeriod
    (period : Nat)
    (pair : (IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell))
    (shift : Cell) :
    Option ((IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell)) :=
  let shifted := occurrencePairSubtractShift pair shift
  if canonicalOrientedOccurrencePairAtPeriod period shifted then
    some shifted
  else
    none

/-- Exactly twenty-five fixed common-shift candidates for one physical
occurrence pair. -/
def occurrencePairCanonicalShiftCandidatesAtPeriod
    (period : Nat)
    (pair : (IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell)) :
    List (Option ((IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell))) :=
  carrierCrossingRetentionShifts.map
    (occurrencePairCanonicalShiftCandidateAtPeriod period pair)

/-- Active canonical crossing records in the fixed shift block. -/
def occurrencePairCanonicalCrossingRecordShiftBlockAtPeriod
    (period : Nat)
    (pair : (IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell)) : List CrossingRecord :=
  (occurrencePairCanonicalShiftCandidatesAtPeriod period pair).filterMap
    (Option.map (occurrencePairCrossingRecordAtPeriod period))

/-- Compact canonical-left source pairs selected by the same fixed block. -/
def occurrencePairCanonicalLeftSourceKeyShiftBlockAtPeriod
    (period : Nat)
    (pair : (IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell)) :
    List CarrierNodeSourceKeys.SourceKeyPair :=
  (occurrencePairCanonicalCrossingRecordShiftBlockAtPeriod period pair).map
    RetainedCompactAtomWords.crossingPair

/-- Concatenate every fixed common-shift block in physical occurrence-product
order. -/
def occurrencePairCanonicalCrossingRecordShiftScanAtPeriod
    (period : Nat)
    (occurrences : List (IndexedGridSegment × Cell)) :
    List CrossingRecord :=
  (occurrences ×ˢ occurrences).flatMap
    (occurrencePairCanonicalCrossingRecordShiftBlockAtPeriod period)

/-- Compact canonical-left pairs in the same physical shift-scan order. -/
def occurrencePairCanonicalLeftSourceKeyShiftScanAtPeriod
    (period : Nat)
    (occurrences : List (IndexedGridSegment × Cell)) :
    List CarrierNodeSourceKeys.SourceKeyPair :=
  (occurrencePairCanonicalCrossingRecordShiftScanAtPeriod
    period occurrences).map RetainedCompactAtomWords.crossingPair

/-- Last-occurrence representatives of the compiled canonical-left source
pairs. -/
def occurrencePairCanonicalLeftSourceKeyShiftScanDedupAtPeriod
    (period : Nat)
    (occurrences : List (IndexedGridSegment × Cell)) :
    List CarrierNodeSourceKeys.SourceKeyPair :=
  (occurrencePairCanonicalLeftSourceKeyShiftScanAtPeriod
    period occurrences).dedup

end LeanTrominoes.PeriodicOrthocrossing
