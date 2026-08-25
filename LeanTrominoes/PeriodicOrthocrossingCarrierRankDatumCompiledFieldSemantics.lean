/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCompiledFieldData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumFieldColumnData

/-! # Abstract semantics of the compiled carrier field enumeration -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankDatumCompiledFields

/-- The generic representative-selected rank columns named by a fixed list of
compiled field indices. -/
def selectedColumnsFor (fields : List Field) (period : Nat)
    (descriptors : List RouteDescriptor) : List (List Nat) :=
  fields.map fun field =>
    CarrierRankDatumLookup.selectedFieldValuesAtPeriod period descriptors
      fun datum => datum.scanUnaryFields.getD field.index 0

@[simp] theorem selectedColumnsFor_append
    (first second : List Field) (period : Nat)
    (descriptors : List RouteDescriptor) :
    selectedColumnsFor (first ++ second) period descriptors =
      selectedColumnsFor first period descriptors ++
      selectedColumnsFor second period descriptors := by
  simp [selectedColumnsFor]

/-- The ordered field enumeration names exactly generic scan indices zero
through forty-nine. -/
theorem selectedColumnsFor_all_eq_selectedAtPeriod
    (period : Nat) (descriptors : List RouteDescriptor) :
    selectedColumnsFor all period descriptors =
      CarrierRankDatumFieldColumns.selectedAtPeriod period descriptors := by
  unfold selectedColumnsFor CarrierRankDatumFieldColumns.selectedAtPeriod
  rw [← all_indices]
  rw [List.map_map]
  apply List.map_congr_left
  intro field _fieldMember
  rfl

end CarrierRankDatumCompiledFields
end LeanTrominoes.PeriodicOrthocrossing
