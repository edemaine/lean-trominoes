/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListMapZipIdxCongr
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedSourceKeyRepresentativeFieldLookupNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalPermutationSemantics
import LeanTrominoes.UnaryPermutationRankBlockLookupSemantics

/-! # Numeric semantics of globally ranked normalized carrier fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierNormalizedSourceKeyRankOrderedFields

private theorem flatMap_eq_flatten_map
    {Source Target : Type*} (items : List Source)
    (blocks : Source → List Target) :
    items.flatMap blocks = (items.map blocks).flatten := by
  induction items with
  | nil => rfl
  | cons item items induction =>
      simp only [List.flatMap_cons, List.map_cons, List.flatten_cons,
        induction]

private theorem flatMap_zipIdx_fst
    {Source Target : Type*} (items : List Source)
    (blocks : Source → List Target) :
    items.zipIdx.flatMap (fun entry => blocks entry.1) =
      items.flatMap blocks := by
  have mapped :
      items.zipIdx.map (fun entry => blocks entry.1) =
        items.map blocks :=
    List.map_zipIdx_eq_map_of_mem items
      (fun entry => blocks entry.1) blocks
      (fun _entry _entryMember => rfl)
  rw [flatMap_eq_flatten_map, flatMap_eq_flatten_map, mapped]

/-- On valid numeric routes, block permutation emits each normalized
source-pair block in exact global key-major, stable-coordinate carrier order. -/
theorem values_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    UnaryPermutationRankBlockLookup.values
        CarrierSourceKeyRepresentativeFieldLookup.fieldCount
        (CarrierRankGlobal.ranks
          (PeriodicCNF.numericRouteDescriptors formula))
        (CarrierNormalizedSourceKeyRepresentativeFieldLookup.selectedFieldsAtPeriod
          (routeDescriptorStreamGridSize
            (PeriodicCNF.numericRouteDescriptors formula))
          (PeriodicCNF.numericRouteDescriptors formula)) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let period := routeDescriptorStreamGridSize descriptors
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod period descriptors).dedup
      (CarrierRankGlobal.enumeration datums).flatMap fun entry =>
        CarrierSourceKeyRepresentativeFieldLookup.sourcePairFields
          (some (CarrierNodeNormalizedSourceKeys.datumPairAtPeriod
            period entry.1)) := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let period := routeDescriptorStreamGridSize descriptors
  let datums :=
    (routeDescriptorCarrierRankDatumsAtPeriod period descriptors).dedup
  let blocks := fun datum =>
    CarrierSourceKeyRepresentativeFieldLookup.sourcePairFields
      (some (CarrierNodeNormalizedSourceKeys.datumPairAtPeriod period datum))
  have rankEq := CarrierRankGlobal.ranks_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty
  have selectedEq :=
    CarrierNormalizedSourceKeyRepresentativeFieldLookup.selectedFieldsAtPeriod_numericRouteDescriptors
      formula wellFormed degree isLocal forward nonempty
  have fieldEq :
      CarrierNormalizedSourceKeyRepresentativeFieldLookup.selectedFieldsAtPeriod
          period descriptors =
        datums.zipIdx.flatMap fun entry => blocks entry.1 := by
    rw [selectedEq]
    exact (flatMap_zipIdx_fst datums blocks).symm
  have rankIndexEq :
      datums.zipIdx.map (CarrierRankGlobal.rankAt datums) =
        datums.zipIdx.map fun entry =>
          @List.idxOf (CarrierNodeRankDatum × Nat)
            instBEqOfDecidableEq entry
            (CarrierRankGlobal.enumeration datums) := by
    apply List.map_congr_left
    intro entry entryMember
    exact CarrierRankGlobal.rankAt_eq_idxOf_enumeration
      datums entry entryMember
  rw [rankEq, fieldEq, rankIndexEq]
  exact UnaryPermutationRankBlockLookup.values_flatMap_idxOf_of_perm
    datums.zipIdx (CarrierRankGlobal.enumeration datums)
    (CarrierRankGlobal.enumeration_perm_zipIdx datums)
    (CarrierRankGlobal.enumeration_nodup datums)
    (fun entry => blocks entry.1)
    CarrierSourceKeyRepresentativeFieldLookup.fieldCount
    (fun entry =>
      CarrierSourceKeyRepresentativeFieldLookup.sourcePairFields_length
        (some (CarrierNodeNormalizedSourceKeys.datumPairAtPeriod
          period entry.1)))

end CarrierNormalizedSourceKeyRankOrderedFields
end LeanTrominoes.PeriodicOrthocrossing
