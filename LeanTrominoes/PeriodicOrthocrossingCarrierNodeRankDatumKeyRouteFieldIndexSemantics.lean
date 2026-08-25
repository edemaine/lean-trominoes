/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeRankDatumUnaryData

/-! # Carrier-key route index in rank scans -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The carrier-key route index is field zero of the fixed zero-indexed
rank-scan record. -/
@[simp] theorem CarrierNodeRankDatum.scanUnaryFields_getD_zero
    (datum : CarrierNodeRankDatum) :
    datum.scanUnaryFields.getD 0 0 = datum.key.1 := by
  simp [CarrierNodeRankDatum.scanUnaryFields,
    CarrierNodeRankDatum.scanDatum, CarrierRankScanDatum.unaryFields,
    carrierKeyUnaryFields]

end LeanTrominoes.PeriodicOrthocrossing
