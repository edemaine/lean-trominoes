/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingPointFieldIndexSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierOwnershipShiftFieldIndexSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCompiledFieldSemantics

/-! # Numeric semantics of carrier rank-scan fields forty-two through forty-nine -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankDatumCompiledFields

theorem suffixColumns_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    suffixColumns (PeriodicCNF.numericRouteDescriptors formula) =
      selectedColumnsFor suffixFields
        (routeDescriptorStreamGridSize
          (PeriodicCNF.numericRouteDescriptors formula))
        (PeriodicCNF.numericRouteDescriptors formula) := by
  unfold suffixColumns columnsFor selectedColumnsFor suffixFields
  simp only [List.map_cons, List.map_nil, Field.values, Field.index]
  rw [CarrierCrossingPointField.values_numericRouteDescriptors_eq_indexedField
    formula wellFormed degree isLocal forward nonempty .horizontalPositive]
  rw [CarrierCrossingPointField.values_numericRouteDescriptors_eq_indexedField
    formula wellFormed degree isLocal forward nonempty .horizontalNegative]
  rw [CarrierCrossingPointField.values_numericRouteDescriptors_eq_indexedField
    formula wellFormed degree isLocal forward nonempty .verticalPositive]
  rw [CarrierCrossingPointField.values_numericRouteDescriptors_eq_indexedField
    formula wellFormed degree isLocal forward nonempty .verticalNegative]
  rw [CarrierOwnershipShiftField.values_numericRouteDescriptors_eq_indexedField
    formula wellFormed degree isLocal forward nonempty .horizontalPositive]
  rw [CarrierOwnershipShiftField.values_numericRouteDescriptors_eq_indexedField
    formula wellFormed degree isLocal forward nonempty .horizontalNegative]
  rw [CarrierOwnershipShiftField.values_numericRouteDescriptors_eq_indexedField
    formula wellFormed degree isLocal forward nonempty .verticalPositive]
  rw [CarrierOwnershipShiftField.values_numericRouteDescriptors_eq_indexedField
    formula wellFormed degree isLocal forward nonempty .verticalNegative]
  simp [CarrierCrossingPointField.index, CarrierOwnershipShiftField.index]

end CarrierRankDatumCompiledFields
end LeanTrominoes.PeriodicOrthocrossing
