/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumLookupData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyFieldData

/-! # Carrier rank values corresponding to physical key fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeyField

/-- Interpret one physical-key selector as a natural-valued rank datum
field. -/
def rankValue : CarrierKeyFieldProjector.Field → CarrierNodeRankDatum → Nat
  | .route, datum => datum.key.1
  | .segment, datum => datum.key.2.1
  | .horizontalPositive, datum => datum.key.2.2.1.toNat
  | .horizontalNegative, datum => (-datum.key.2.2.1).toNat
  | .verticalPositive, datum => datum.key.2.2.2.toNat
  | .verticalNegative, datum => (-datum.key.2.2.2).toNat

/-- Zero-indexed rank-scan position of each physical carrier-key column. -/
def index : CarrierKeyFieldProjector.Field → Nat
  | .route => 0
  | .segment => 1
  | .horizontalPositive => 2
  | .horizontalNegative => 3
  | .verticalPositive => 4
  | .verticalNegative => 5

end CarrierRankKeyField
end LeanTrominoes.PeriodicOrthocrossing
