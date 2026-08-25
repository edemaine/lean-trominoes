/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderFieldNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderStrictLowerCompiler
import LeanTrominoes.SignedUnaryStrictLowerSemantics

/-! # Numeric semantics of carrier-rank strict order comparisons -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderStrictLower

/-- On valid numeric routes, the compiled matrix marks exactly the ordered
pairs whose second carrier-rank datum has smaller order coordinate. -/
theorem bits_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    bits (PeriodicCNF.numericRouteDescriptors formula) =
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize
            (PeriodicCNF.numericRouteDescriptors formula))
          (PeriodicCNF.numericRouteDescriptors formula)).dedup
      datums.flatMap fun first =>
        datums.map fun second =>
          decide (second.orderCoordinate < first.orderCoordinate) := by
  unfold bits
  rw [CarrierRankOrderField.values_numericRouteDescriptors
      formula wellFormed degree isLocal forward nonempty true,
    CarrierRankOrderField.values_numericRouteDescriptors
      formula wellFormed degree isLocal forward nonempty false,
    CarrierRankDatumLookup.selectedFieldValuesAtPeriod_numericRouteDescriptors
      formula wellFormed degree isLocal forward nonempty
      (carrierRankOrderField true),
    CarrierRankDatumLookup.selectedFieldValuesAtPeriod_numericRouteDescriptors
      formula wellFormed degree isLocal forward nonempty
      (carrierRankOrderField false)]
  have positiveFieldEq :
      carrierRankOrderField true =
        fun datum => datum.orderCoordinate.toNat :=
    funext carrierRankOrderField_true
  have negativeFieldEq :
      carrierRankOrderField false =
        fun datum => (-datum.orderCoordinate).toNat :=
    funext carrierRankOrderField_false
  rw [positiveFieldEq, negativeFieldEq]
  simpa [SignedUnaryStrictLower.positiveMagnitude,
      SignedUnaryStrictLower.negativeMagnitude, List.map_map,
      List.flatMap_map, Function.comp_def] using
    SignedUnaryStrictLower.strictLowerBits_magnitudes
      ((routeDescriptorCarrierRankDatumsAtPeriod
        (routeDescriptorStreamGridSize
          (PeriodicCNF.numericRouteDescriptors formula))
        (PeriodicCNF.numericRouteDescriptors formula)).dedup.map
          CarrierNodeRankDatum.orderCoordinate)

end CarrierRankOrderStrictLower
end LeanTrominoes.PeriodicOrthocrossing
