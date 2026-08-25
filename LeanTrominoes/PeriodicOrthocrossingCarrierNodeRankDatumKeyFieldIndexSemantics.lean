/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeRankDatumUnaryData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyFieldRankValueData

/-! # Physical carrier-key columns in rank scans -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeyField

/-- The six physical-key selectors are exactly zero-indexed rank-scan
columns zero through five. -/
@[simp] theorem scanUnaryFields_getD_index
    (field : CarrierKeyFieldProjector.Field)
    (datum : CarrierNodeRankDatum) :
    datum.scanUnaryFields.getD (index field) 0 = rankValue field datum := by
  cases field <;>
    simp [index, rankValue, CarrierNodeRankDatum.scanUnaryFields,
      CarrierNodeRankDatum.scanDatum, CarrierRankScanDatum.unaryFields,
      carrierKeyUnaryFields, cellUnaryFields, signedUnaryFields]

end CarrierRankKeyField
end LeanTrominoes.PeriodicOrthocrossing
