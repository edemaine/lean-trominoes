/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPresenceFieldIndexSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizationOffsetFieldIndexSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCompiledFieldSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankHorizontalFieldIndexSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyRouteFieldIndexSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeySegmentFieldIndexSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeySignedFieldsIndexSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderFieldIndexSemantics

/-! # Numeric semantics of carrier rank-scan fields zero through thirteen -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankDatumCompiledFields

theorem prefixColumns_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    prefixColumns (PeriodicCNF.numericRouteDescriptors formula) =
      selectedColumnsFor prefixFields
        (routeDescriptorStreamGridSize
          (PeriodicCNF.numericRouteDescriptors formula))
        (PeriodicCNF.numericRouteDescriptors formula) := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let period := routeDescriptorStreamGridSize descriptors
  unfold prefixColumns columnsFor selectedColumnsFor prefixFields
  simp only [List.map_cons, List.map_nil, Field.values, Field.index]
  rw [CarrierRankKeyRouteField.values_eq_fieldZero period descriptors]
  rw [CarrierRankKeySegmentField.values_eq_fieldOne period descriptors]
  rw [CarrierRankKeySignedFields.horizontalPositiveValues_eq_fieldTwo
    period descriptors]
  rw [CarrierRankKeySignedFields.horizontalNegativeValues_eq_fieldThree
    period descriptors]
  rw [CarrierRankKeySignedFields.verticalPositiveValues_eq_fieldFour
    period descriptors]
  rw [CarrierRankKeySignedFields.verticalNegativeValues_eq_fieldFive
    period descriptors]
  rw [CarrierRankOrderField.positiveValues_numericRouteDescriptors_eq_fieldSix
    formula wellFormed degree isLocal forward nonempty]
  rw [CarrierRankOrderField.negativeValues_numericRouteDescriptors_eq_fieldSeven
    formula wellFormed degree isLocal forward nonempty]
  rw [CarrierRankHorizontalField.values_numericRouteDescriptors_eq_fieldEight
    formula wellFormed degree isLocal forward nonempty]
  rw [CarrierNormalizationOffsetField.values_numericRouteDescriptors_eq_indexedField
    formula wellFormed degree isLocal forward nonempty .horizontalPositive]
  rw [CarrierNormalizationOffsetField.values_numericRouteDescriptors_eq_indexedField
    formula wellFormed degree isLocal forward nonempty .horizontalNegative]
  rw [CarrierNormalizationOffsetField.values_numericRouteDescriptors_eq_indexedField
    formula wellFormed degree isLocal forward nonempty .verticalPositive]
  rw [CarrierNormalizationOffsetField.values_numericRouteDescriptors_eq_indexedField
    formula wellFormed degree isLocal forward nonempty .verticalNegative]
  rw [CarrierBoundaryPresenceField.values_eq_fieldThirteen period descriptors]
  simp [descriptors, period, CarrierNormalizationOffsetField.index]

end CarrierRankDatumCompiledFields
end LeanTrominoes.PeriodicOrthocrossing
