/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingIndexedSegmentFieldIndexSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingRecordSourceFieldIndexSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCompiledFieldSemantics

/-! # Numeric semantics of carrier rank-scan fields fourteen through twenty-seven -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankDatumCompiledFields

theorem firstCrossingColumns_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    firstCrossingColumns (PeriodicCNF.numericRouteDescriptors formula) =
      selectedColumnsFor firstCrossingFields
        (routeDescriptorStreamGridSize
          (PeriodicCNF.numericRouteDescriptors formula))
        (PeriodicCNF.numericRouteDescriptors formula) := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let period := routeDescriptorStreamGridSize descriptors
  unfold firstCrossingColumns columnsFor selectedColumnsFor firstCrossingFields
  simp only [List.map_cons, List.map_nil, Field.values, Field.index]
  rw [CarrierCrossingRecordSourceField.values_eq_indexedField
    .firstRoute period descriptors]
  rw [CarrierCrossingIndexedSegmentField.values_numericRouteDescriptors_eq_indexedField
    formula wellFormed degree isLocal forward nonempty .firstSegmentIndex]
  rw [CarrierCrossingIndexedSegmentField.values_numericRouteDescriptors_eq_indexedField
    formula wellFormed degree isLocal forward nonempty
      (.coordinate .first .start true true)]
  rw [CarrierCrossingIndexedSegmentField.values_numericRouteDescriptors_eq_indexedField
    formula wellFormed degree isLocal forward nonempty
      (.coordinate .first .start true false)]
  rw [CarrierCrossingIndexedSegmentField.values_numericRouteDescriptors_eq_indexedField
    formula wellFormed degree isLocal forward nonempty
      (.coordinate .first .start false true)]
  rw [CarrierCrossingIndexedSegmentField.values_numericRouteDescriptors_eq_indexedField
    formula wellFormed degree isLocal forward nonempty
      (.coordinate .first .start false false)]
  rw [CarrierCrossingIndexedSegmentField.values_numericRouteDescriptors_eq_indexedField
    formula wellFormed degree isLocal forward nonempty
      (.coordinate .first .finish true true)]
  rw [CarrierCrossingIndexedSegmentField.values_numericRouteDescriptors_eq_indexedField
    formula wellFormed degree isLocal forward nonempty
      (.coordinate .first .finish true false)]
  rw [CarrierCrossingIndexedSegmentField.values_numericRouteDescriptors_eq_indexedField
    formula wellFormed degree isLocal forward nonempty
      (.coordinate .first .finish false true)]
  rw [CarrierCrossingIndexedSegmentField.values_numericRouteDescriptors_eq_indexedField
    formula wellFormed degree isLocal forward nonempty
      (.coordinate .first .finish false false)]
  rw [CarrierCrossingRecordSourceField.values_eq_indexedField
    .firstTranslateHorizontalPositive period descriptors]
  rw [CarrierCrossingRecordSourceField.values_eq_indexedField
    .firstTranslateHorizontalNegative period descriptors]
  rw [CarrierCrossingRecordSourceField.values_eq_indexedField
    .firstTranslateVerticalPositive period descriptors]
  rw [CarrierCrossingRecordSourceField.values_eq_indexedField
    .firstTranslateVerticalNegative period descriptors]
  simp [descriptors, period, CarrierCrossingRecordSourceField.index,
    CarrierCrossingIndexedSegmentField.index,
    CarrierCrossingIndexedSegmentField.coordinateBase,
    CarrierCrossingIndexedSegmentField.coordinateOffset]

end CarrierRankDatumCompiledFields
end LeanTrominoes.PeriodicOrthocrossing
