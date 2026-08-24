/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairRetainedCarrierKeyScanData

/-! # Graph-free retained carrier keys of occurrence pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Four retained carrier-key copies obtained from an occurrence pair under
one common period shift. -/
def occurrencePairCarrierKeyShiftBlock
    (pair : (IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell))
    (shift : Cell) : List (Nat × Nat × Cell) :=
  let horizontal := occurrenceCarrierKey
    (pair.1.1, Cell.add pair.1.2 shift)
  let vertical := occurrenceCarrierKey
    (pair.2.1, Cell.add pair.2.2 shift)
  [horizontal, horizontal, vertical, vertical]

/-- Fixed retention-window carrier-key block of one occurrence pair. -/
def occurrencePairCarrierKeyBlock
    (pair : (IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell)) : List (Nat × Nat × Cell) :=
  carrierCrossingRetentionShifts.flatMap
    (occurrencePairCarrierKeyShiftBlock pair)

/-- Graph-free expansion of an ordered occurrence-pair stream. -/
def occurrencePairCarrierKeyScan
    (pairs : List ((IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell))) : List (Nat × Nat × Cell) :=
  pairs.flatMap occurrencePairCarrierKeyBlock

end LeanTrominoes.PeriodicOrthocrossing
