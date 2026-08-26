/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListMapZipIdxCongr
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCompiledColumnNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCompiledRankOrderedFieldData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalPermutationSemantics
import LeanTrominoes.UnaryPermutationRankLookupEnumerationSemantics

/-! # Numeric semantics of globally rank-ordered carrier datum fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankDatumCompiledFields

private theorem all_getElem?_index (field : Field) :
    all[field.index]? = some field := by
  cases field <;> native_decide

private theorem range_getElem?_index (field : Field) :
    (List.range 50)[field.index]? = some field.index := by
  cases field <;> native_decide

/-- On valid numeric routes, every named compiler field is the corresponding
field of every compact carrier rank datum in presentation order. -/
theorem Field.values_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (field : Field)
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    field.values (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize descriptors) descriptors).dedup
      datums.zipIdx.map fun entry =>
        entry.1.scanUnaryFields.getD field.index 0 := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let datums :=
    (routeDescriptorCarrierRankDatumsAtPeriod
      (routeDescriptorStreamGridSize descriptors) descriptors).dedup
  have columnEq := columns_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty
  have selected := congrArg (fun columns => columns[field.index]?) columnEq
  change
    (all.map fun selectedField =>
      selectedField.values descriptors)[field.index]? =
    ((List.range 50).map fun fieldIndex =>
      datums.map fun datum =>
        datum.scanUnaryFields.getD fieldIndex 0)[field.index]? at selected
  simp only [List.getElem?_map, all_getElem?_index,
    range_getElem?_index, Option.map_some] at selected
  have presentedEq :
      field.values descriptors =
        datums.map fun datum =>
          datum.scanUnaryFields.getD field.index 0 :=
    Option.some.inj selected
  rw [presentedEq]
  symm
  exact List.map_zipIdx_eq_map_of_mem datums
    (fun entry => entry.1.scanUnaryFields.getD field.index 0)
    (fun datum => datum.scanUnaryFields.getD field.index 0)
    (fun _entry _entryMember => rfl)

/-- On valid numeric routes, the compiled lookup emits the selected carrier
datum field in the exact global key-major, stable-coordinate enumeration. -/
theorem Field.rankOrderedValues_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (field : Field)
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    field.rankOrderedValues (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize descriptors) descriptors).dedup
      (CarrierRankGlobal.enumeration datums).map fun entry =>
        entry.1.scanUnaryFields.getD field.index 0 := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let datums :=
    (routeDescriptorCarrierRankDatumsAtPeriod
      (routeDescriptorStreamGridSize descriptors) descriptors).dedup
  have fieldEq := field.values_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty
  have rankEq := CarrierRankGlobal.ranks_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty
  have rankIndexEq :
      datums.zipIdx.map (CarrierRankGlobal.rankAt datums) =
        datums.zipIdx.map fun entry =>
          @List.idxOf (CarrierNodeRankDatum × Nat) instBEqOfDecidableEq
            entry (CarrierRankGlobal.enumeration datums) := by
    apply List.map_congr_left
    intro entry entryMember
    exact CarrierRankGlobal.rankAt_eq_idxOf_enumeration
      datums entry entryMember
  unfold Field.rankOrderedValues
  change UnaryPermutationRankLookup.values
      (CarrierRankGlobal.ranks descriptors) (field.values descriptors) = _
  rw [rankEq, fieldEq, rankIndexEq]
  exact UnaryPermutationRankLookup.values_map_idxOf_of_perm
    datums.zipIdx (CarrierRankGlobal.enumeration datums)
    (CarrierRankGlobal.enumeration_perm_zipIdx datums)
    (CarrierRankGlobal.enumeration_nodup datums)
    (fun entry => entry.1.scanUnaryFields.getD field.index 0)

end CarrierRankDatumCompiledFields
end LeanTrominoes.PeriodicOrthocrossing
