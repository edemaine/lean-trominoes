/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeRankDatumUnaryData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumLookupData

/-! # Column-major selected carrier rank fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankDatumFieldColumns

/-- Fifty selected lookup columns, one for every field of the identity-free
carrier rank-scan record. -/
def selectedAtPeriod (period : Nat)
    (descriptors : List RouteDescriptor) : List (List Nat) :=
  (List.range 50).map fun fieldIndex =>
    CarrierRankDatumLookup.selectedFieldValuesAtPeriod
      period descriptors fun datum =>
        datum.scanUnaryFields.getD fieldIndex 0

/-- The corresponding exact column-major view of any already-deduplicated
rank-datum list. -/
def ofRankDatums (datums : List CarrierNodeRankDatum) : List (List Nat) :=
  (List.range 50).map fun fieldIndex =>
    datums.map fun datum => datum.scanUnaryFields.getD fieldIndex 0

end CarrierRankDatumFieldColumns
end LeanTrominoes.PeriodicOrthocrossing
