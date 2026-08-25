/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingIndexedSegmentFieldIndexSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingRecordSourceFieldIndexSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCompiledFieldSemantics

/-! # Numeric semantics of carrier rank-scan fields twenty-eight through forty-one -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankDatumCompiledFields

theorem secondCrossingColumns_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    secondCrossingColumns (PeriodicCNF.numericRouteDescriptors formula) =
      selectedColumnsFor secondCrossingFields
        (routeDescriptorStreamGridSize
          (PeriodicCNF.numericRouteDescriptors formula))
        (PeriodicCNF.numericRouteDescriptors formula) := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let period := routeDescriptorStreamGridSize descriptors
  unfold secondCrossingColumns columnsFor selectedColumnsFor
    secondCrossingFields
  simp only [List.map_cons, List.map_nil, Field.values, Field.index]
  rw [CarrierCrossingRecordSourceField.values_eq_indexedField
    .secondRoute period descriptors]
  rw [CarrierCrossingRecordSourceField.values_eq_indexedField
    .secondSegment period descriptors]
  rw [CarrierCrossingIndexedSegmentField.values_numericRouteDescriptors_eq_indexedField
    formula wellFormed degree isLocal forward nonempty
      (.coordinate .second .start true true)]
  rw [CarrierCrossingIndexedSegmentField.values_numericRouteDescriptors_eq_indexedField
    formula wellFormed degree isLocal forward nonempty
      (.coordinate .second .start true false)]
  rw [CarrierCrossingIndexedSegmentField.values_numericRouteDescriptors_eq_indexedField
    formula wellFormed degree isLocal forward nonempty
      (.coordinate .second .start false true)]
  rw [CarrierCrossingIndexedSegmentField.values_numericRouteDescriptors_eq_indexedField
    formula wellFormed degree isLocal forward nonempty
      (.coordinate .second .start false false)]
  rw [CarrierCrossingIndexedSegmentField.values_numericRouteDescriptors_eq_indexedField
    formula wellFormed degree isLocal forward nonempty
      (.coordinate .second .finish true true)]
  rw [CarrierCrossingIndexedSegmentField.values_numericRouteDescriptors_eq_indexedField
    formula wellFormed degree isLocal forward nonempty
      (.coordinate .second .finish true false)]
  rw [CarrierCrossingIndexedSegmentField.values_numericRouteDescriptors_eq_indexedField
    formula wellFormed degree isLocal forward nonempty
      (.coordinate .second .finish false true)]
  rw [CarrierCrossingIndexedSegmentField.values_numericRouteDescriptors_eq_indexedField
    formula wellFormed degree isLocal forward nonempty
      (.coordinate .second .finish false false)]
  rw [CarrierCrossingRecordSourceField.values_eq_indexedField
    .secondTranslateHorizontalPositive period descriptors]
  rw [CarrierCrossingRecordSourceField.values_eq_indexedField
    .secondTranslateHorizontalNegative period descriptors]
  rw [CarrierCrossingRecordSourceField.values_eq_indexedField
    .secondTranslateVerticalPositive period descriptors]
  rw [CarrierCrossingRecordSourceField.values_eq_indexedField
    .secondTranslateVerticalNegative period descriptors]
  simp [descriptors, period, CarrierCrossingRecordSourceField.index,
    CarrierCrossingIndexedSegmentField.index,
    CarrierCrossingIndexedSegmentField.coordinateBase,
    CarrierCrossingIndexedSegmentField.coordinateOffset]

end CarrierRankDatumCompiledFields
end LeanTrominoes.PeriodicOrthocrossing
