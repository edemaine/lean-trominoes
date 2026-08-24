/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeRankDatumUnaryData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankHorizontalFieldNumericSemantics

/-! # Horizontal field index in carrier rank scans -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The horizontal bit is field eight of the fixed zero-indexed rank-scan
record. -/
@[simp] theorem CarrierNodeRankDatum.scanUnaryFields_getD_eight
    (datum : CarrierNodeRankDatum) :
    datum.scanUnaryFields.getD 8 0 =
      (if datum.horizontal then 1 else 0) := by
  simp [CarrierNodeRankDatum.scanUnaryFields,
    CarrierNodeRankDatum.scanDatum, CarrierRankScanDatum.unaryFields,
    carrierKeyUnaryFields, cellUnaryFields, signedUnaryFields]

namespace CarrierRankHorizontalField

/-- The compiled horizontal lookup is precisely selected rank-scan column
eight on valid numeric routes. -/
theorem values_numericRouteDescriptors_eq_fieldEight
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    values (PeriodicCNF.numericRouteDescriptors formula) =
      CarrierRankDatumLookup.selectedFieldValuesAtPeriod
        (routeDescriptorStreamGridSize
          (PeriodicCNF.numericRouteDescriptors formula))
        (PeriodicCNF.numericRouteDescriptors formula)
        (fun datum => datum.scanUnaryFields.getD 8 0) := by
  rw [values_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty]
  congr 1

end CarrierRankHorizontalField
end LeanTrominoes.PeriodicOrthocrossing
