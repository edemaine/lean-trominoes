/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeRankDatumUnaryData

/-! # Lengths of fixed carrier rank-scan fields -/

namespace LeanTrominoes.PeriodicOrthocrossing

@[simp] theorem signedUnaryFields_length (value : Int) :
    (signedUnaryFields value).length = 2 :=
  rfl

@[simp] theorem cellUnaryFields_length (cell : Cell) :
    (cellUnaryFields cell).length = 4 := by
  simp [cellUnaryFields]

@[simp] theorem IndexedGridSegmentCode.scanUnaryFields_length
    (code : IndexedGridSegmentCode) :
    code.scanUnaryFields.length = 10 := by
  simp [IndexedGridSegmentCode.scanUnaryFields]

@[simp] theorem CrossingRecordCode.scanUnaryFields_length
    (code : CrossingRecordCode) :
    code.scanUnaryFields.length = 32 := by
  simp [CrossingRecordCode.scanUnaryFields]

@[simp] theorem optionalCrossingRecordCodeUnaryFields_length
    (code : Option CrossingRecordCode) :
    (optionalCrossingRecordCodeUnaryFields code).length = 33 := by
  cases code <;> simp [optionalCrossingRecordCodeUnaryFields]

@[simp] theorem carrierKeyUnaryFields_length
    (key : Nat × Nat × Cell) :
    (carrierKeyUnaryFields key).length = 6 := by
  simp [carrierKeyUnaryFields]

@[simp] theorem CarrierRankScanDatum.unaryFields_length
    (datum : CarrierRankScanDatum) :
    datum.unaryFields.length = 50 := by
  simp [CarrierRankScanDatum.unaryFields]

@[simp] theorem CarrierNodeRankDatum.scanUnaryFields_length
    (datum : CarrierNodeRankDatum) :
    datum.scanUnaryFields.length = 50 := by
  simp [CarrierNodeRankDatum.scanUnaryFields]

end LeanTrominoes.PeriodicOrthocrossing
