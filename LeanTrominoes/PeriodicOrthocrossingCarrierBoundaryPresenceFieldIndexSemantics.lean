/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPresenceFieldSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeRankDatumUnaryData

/-! # Boundary-presence field index in carrier rank scans -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Boundary-crossing presence is field thirteen of the fixed zero-indexed
rank-scan record. -/
@[simp] theorem CarrierNodeRankDatum.scanUnaryFields_getD_thirteen
    (datum : CarrierNodeRankDatum) :
    datum.scanUnaryFields.getD 13 0 =
      CarrierBoundaryPresenceField.rankValue datum := by
  cases boundaryCrossingEq : datum.boundaryCrossing <;>
    simp [CarrierNodeRankDatum.scanUnaryFields,
      CarrierNodeRankDatum.scanDatum, CarrierRankScanDatum.unaryFields,
      carrierKeyUnaryFields, cellUnaryFields, signedUnaryFields,
      optionalCrossingRecordCodeUnaryFields,
      CarrierBoundaryPresenceField.rankValue, boundaryCrossingEq]

namespace CarrierBoundaryPresenceField

/-- The compiled boundary-presence lookup is precisely selected rank-scan
column thirteen. -/
theorem values_eq_fieldThirteen
    (period : Nat) (descriptors : List RouteDescriptor) :
    values descriptors =
      CarrierRankDatumLookup.selectedFieldValuesAtPeriod
        period descriptors
        (fun datum => datum.scanUnaryFields.getD 13 0) := by
  rw [values_eq_selectedFieldValuesAtPeriod]
  congr 1
  funext datum
  exact datum.scanUnaryFields_getD_thirteen.symm

end CarrierBoundaryPresenceField
end LeanTrominoes.PeriodicOrthocrossing
