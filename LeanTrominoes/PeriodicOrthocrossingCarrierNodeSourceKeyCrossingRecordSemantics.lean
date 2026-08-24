/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyData
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairRetainedCrossingRecordData

/-! # Reconstruction of retained crossings from their final occurrences -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Translating a reconstructed crossing record is the same as reconstructing
the crossing directly from its two translated occurrence keys. -/
theorem crossingRecordPeriodTranslateAtPeriod_occurrencePairCrossingRecord
    (period : Nat)
    (pair : (IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell))
    (shift : Cell) :
    crossingRecordPeriodTranslateAtPeriod period
        (occurrencePairCrossingRecordAtPeriod period pair) shift =
      occurrencePairCrossingRecordAtPeriod period
        ((pair.1.1, Cell.add pair.1.2 shift),
          (pair.2.1, Cell.add pair.2.2 shift)) := by
  rcases pair with ⟨⟨first, firstTranslate⟩,
    ⟨second, secondTranslate⟩⟩
  rcases firstTranslate with ⟨firstX, firstY⟩
  rcases secondTranslate with ⟨secondX, secondY⟩
  rcases shift with ⟨shiftX, shiftY⟩
  simp [crossingRecordPeriodTranslateAtPeriod,
    occurrencePairCrossingRecordAtPeriod, occurrenceSegmentAtPeriod,
    orientedIntersectionPoint, GridSegment.translate, Cell.add, Cell.scale]
  constructor <;> ring

end LeanTrominoes.PeriodicOrthocrossing
