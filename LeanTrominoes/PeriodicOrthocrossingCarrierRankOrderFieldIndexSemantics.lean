/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeRankDatumUnaryData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderFieldNumericSemantics

/-! # Signed order-coordinate indices in carrier rank scans -/

namespace LeanTrominoes.PeriodicOrthocrossing

@[simp] theorem CarrierNodeRankDatum.scanUnaryFields_getD_six
    (datum : CarrierNodeRankDatum) :
    datum.scanUnaryFields.getD 6 0 = datum.orderCoordinate.toNat := by
  simp [CarrierNodeRankDatum.scanUnaryFields,
    CarrierNodeRankDatum.scanDatum, CarrierRankScanDatum.unaryFields,
    carrierKeyUnaryFields, cellUnaryFields, signedUnaryFields]

@[simp] theorem CarrierNodeRankDatum.scanUnaryFields_getD_seven
    (datum : CarrierNodeRankDatum) :
    datum.scanUnaryFields.getD 7 0 = (-datum.orderCoordinate).toNat := by
  simp [CarrierNodeRankDatum.scanUnaryFields,
    CarrierNodeRankDatum.scanDatum, CarrierRankScanDatum.unaryFields,
    carrierKeyUnaryFields, cellUnaryFields, signedUnaryFields]

namespace CarrierRankOrderField

/-- The positive order-coordinate magnitude is rank-scan field six. -/
theorem positiveValues_numericRouteDescriptors_eq_fieldSix
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    values true (PeriodicCNF.numericRouteDescriptors formula) =
      CarrierRankDatumLookup.selectedFieldValuesAtPeriod
        (routeDescriptorStreamGridSize
          (PeriodicCNF.numericRouteDescriptors formula))
        (PeriodicCNF.numericRouteDescriptors formula)
        (fun datum => datum.scanUnaryFields.getD 6 0) := by
  rw [values_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty true]
  congr 1

/-- The negative order-coordinate magnitude is rank-scan field seven. -/
theorem negativeValues_numericRouteDescriptors_eq_fieldSeven
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    values false (PeriodicCNF.numericRouteDescriptors formula) =
      CarrierRankDatumLookup.selectedFieldValuesAtPeriod
        (routeDescriptorStreamGridSize
          (PeriodicCNF.numericRouteDescriptors formula))
        (PeriodicCNF.numericRouteDescriptors formula)
        (fun datum => datum.scanUnaryFields.getD 7 0) := by
  rw [values_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty false]
  congr 1

end CarrierRankOrderField
end LeanTrominoes.PeriodicOrthocrossing
