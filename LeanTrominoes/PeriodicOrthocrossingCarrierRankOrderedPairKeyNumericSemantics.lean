/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeRankDatumKeyFieldIndexSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCompiledRankOrderedFieldNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyEqualityNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPairData
import LeanTrominoes.SignedUnaryEqualitySemantics

/-! # Numeric semantics of rank-ordered carrier-key equality -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

open CarrierRankDatumCompiledFields
open SignedUnaryStrictLower

private theorem map_scanUnaryFields_keyField
    (entries : List (CarrierNodeRankDatum × Nat))
    (field : CarrierKeyFieldProjector.Field) :
    entries.map (fun entry => entry.1.scanUnaryFields.getD
        (CarrierRankKeyField.index field) 0) =
      entries.map fun entry => CarrierRankKeyField.rankValue field entry.1 := by
  apply List.map_congr_left
  intro entry _entryMember
  exact CarrierRankKeyField.scanUnaryFields_getD_index field entry.1

private theorem fieldEqualityBits_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (compiledField : Field)
    (keyField : CarrierKeyFieldProjector.Field)
    (indexEq : compiledField.index = CarrierRankKeyField.index keyField)
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    fieldEqualityBits compiledField
        (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize descriptors) descriptors).dedup
      let entries := CarrierRankGlobal.enumeration datums
      matrix entries fun first second =>
        decide (CarrierRankKeyField.rankValue keyField first.1 =
          CarrierRankKeyField.rankValue keyField second.1) := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let datums :=
    (routeDescriptorCarrierRankDatumsAtPeriod
      (routeDescriptorStreamGridSize descriptors) descriptors).dedup
  let entries := CarrierRankGlobal.enumeration datums
  have valuesEq := compiledField.rankOrderedValues_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty
  change compiledField.rankOrderedValues descriptors =
    entries.map fun entry =>
      entry.1.scanUnaryFields.getD compiledField.index 0 at valuesEq
  unfold fieldEqualityBits
  rw [valuesEq, UnaryFieldEqualityRows.equalityBits_eq_flatMap]
  unfold matrix matrixRows
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro first _firstMember
  rw [List.map_map]
  apply List.map_congr_left
  intro second _secondMember
  simp only [Function.comp_apply]
  rw [indexEq, CarrierRankKeyField.scanUnaryFields_getD_index,
    CarrierRankKeyField.scanUnaryFields_getD_index]

private theorem horizontalTranslationEqualityBits_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    horizontalTranslationEqualityBits
        (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize descriptors) descriptors).dedup
      let entries := CarrierRankGlobal.enumeration datums
      matrix entries fun first second =>
        decide (first.1.key.2.2.1 = second.1.key.2.2.1) := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let datums :=
    (routeDescriptorCarrierRankDatumsAtPeriod
      (routeDescriptorStreamGridSize descriptors) descriptors).dedup
  let entries := CarrierRankGlobal.enumeration datums
  have positiveEq :=
    Field.rankOrderedValues_numericRouteDescriptors
      .keyTranslateHorizontalPositive formula wellFormed degree isLocal
      forward nonempty
  have negativeEq :=
    Field.rankOrderedValues_numericRouteDescriptors
      .keyTranslateHorizontalNegative formula wellFormed degree isLocal
      forward nonempty
  change Field.rankOrderedValues .keyTranslateHorizontalPositive descriptors =
    entries.map fun entry => entry.1.scanUnaryFields.getD 2 0 at positiveEq
  change Field.rankOrderedValues .keyTranslateHorizontalNegative descriptors =
    entries.map fun entry => entry.1.scanUnaryFields.getD 3 0 at negativeEq
  unfold horizontalTranslationEqualityBits
  rw [positiveEq, negativeEq]
  change SignedUnaryEquality.equalityBits
      (entries.map fun entry => entry.1.scanUnaryFields.getD
        (CarrierRankKeyField.index .horizontalPositive) 0)
      (entries.map fun entry => entry.1.scanUnaryFields.getD
        (CarrierRankKeyField.index .horizontalNegative) 0) = _
  rw [map_scanUnaryFields_keyField entries .horizontalPositive,
    map_scanUnaryFields_keyField entries .horizontalNegative]
  simpa [CarrierRankKeyField.rankValue,
      SignedUnaryStrictLower.positiveMagnitude,
      SignedUnaryStrictLower.negativeMagnitude] using
    SignedUnaryEquality.equalityBits_mapped_magnitudes entries
      (fun entry => entry.1.key.2.2.1)

private theorem verticalTranslationEqualityBits_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    verticalTranslationEqualityBits
        (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize descriptors) descriptors).dedup
      let entries := CarrierRankGlobal.enumeration datums
      matrix entries fun first second =>
        decide (first.1.key.2.2.2 = second.1.key.2.2.2) := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let datums :=
    (routeDescriptorCarrierRankDatumsAtPeriod
      (routeDescriptorStreamGridSize descriptors) descriptors).dedup
  let entries := CarrierRankGlobal.enumeration datums
  have positiveEq :=
    Field.rankOrderedValues_numericRouteDescriptors
      .keyTranslateVerticalPositive formula wellFormed degree isLocal
      forward nonempty
  have negativeEq :=
    Field.rankOrderedValues_numericRouteDescriptors
      .keyTranslateVerticalNegative formula wellFormed degree isLocal
      forward nonempty
  change Field.rankOrderedValues .keyTranslateVerticalPositive descriptors =
    entries.map fun entry => entry.1.scanUnaryFields.getD 4 0 at positiveEq
  change Field.rankOrderedValues .keyTranslateVerticalNegative descriptors =
    entries.map fun entry => entry.1.scanUnaryFields.getD 5 0 at negativeEq
  unfold verticalTranslationEqualityBits
  rw [positiveEq, negativeEq]
  change SignedUnaryEquality.equalityBits
      (entries.map fun entry => entry.1.scanUnaryFields.getD
        (CarrierRankKeyField.index .verticalPositive) 0)
      (entries.map fun entry => entry.1.scanUnaryFields.getD
        (CarrierRankKeyField.index .verticalNegative) 0) = _
  rw [map_scanUnaryFields_keyField entries .verticalPositive,
    map_scanUnaryFields_keyField entries .verticalNegative]
  simpa [CarrierRankKeyField.rankValue,
      SignedUnaryStrictLower.positiveMagnitude,
      SignedUnaryStrictLower.negativeMagnitude] using
    SignedUnaryEquality.equalityBits_mapped_magnitudes entries
      (fun entry => entry.1.key.2.2.2)

private theorem indexEqualityBits_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    indexEqualityBits (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize descriptors) descriptors).dedup
      let entries := CarrierRankGlobal.enumeration datums
      matrix entries fun first second =>
        decide ((first.1.key.1, first.1.key.2.1) =
          (second.1.key.1, second.1.key.2.1)) := by
  unfold indexEqualityBits combined
  change pairwise .conjunction
      (fieldEqualityBits .keyRoute
        (PeriodicCNF.numericRouteDescriptors formula))
      (fieldEqualityBits .keySegment
        (PeriodicCNF.numericRouteDescriptors formula)) = _
  rw [fieldEqualityBits_numericRouteDescriptors .keyRoute .route rfl
      formula wellFormed degree isLocal forward nonempty,
    fieldEqualityBits_numericRouteDescriptors .keySegment .segment rfl
      formula wellFormed degree isLocal forward nonempty,
    pairwise_matrix]
  unfold matrix matrixRows
  apply List.flatMap_congr
  intro first _firstMember
  apply List.map_congr_left
  intro second _secondMember
  change (decide (first.1.key.1 = second.1.key.1) &&
      decide (first.1.key.2.1 = second.1.key.2.1)) = _
  exact CarrierRankKeyEquality.decide_prod_eq
    (first.1.key.1, first.1.key.2.1)
    (second.1.key.1, second.1.key.2.1)

private theorem translationEqualityBits_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    translationEqualityBits (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize descriptors) descriptors).dedup
      let entries := CarrierRankGlobal.enumeration datums
      matrix entries fun first second =>
        decide (first.1.key.2.2 = second.1.key.2.2) := by
  unfold translationEqualityBits combined
  change pairwise .conjunction
      (horizontalTranslationEqualityBits
        (PeriodicCNF.numericRouteDescriptors formula))
      (verticalTranslationEqualityBits
        (PeriodicCNF.numericRouteDescriptors formula)) = _
  rw [horizontalTranslationEqualityBits_numericRouteDescriptors
      formula wellFormed degree isLocal forward nonempty,
    verticalTranslationEqualityBits_numericRouteDescriptors
      formula wellFormed degree isLocal forward nonempty,
    pairwise_matrix]
  unfold matrix matrixRows
  apply List.flatMap_congr
  intro first _firstMember
  apply List.map_congr_left
  intro second _secondMember
  change (decide (first.1.key.2.2.1 = second.1.key.2.2.1) &&
      decide (first.1.key.2.2.2 = second.1.key.2.2.2)) = _
  exact CarrierRankKeyEquality.decide_prod_eq
    first.1.key.2.2 second.1.key.2.2

/-- On numeric routes, the rank-ordered six-field equality square is exactly
same-carrier equality on the global enumeration. -/
theorem sameKeyBits_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    sameKeyBits (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize descriptors) descriptors).dedup
      let entries := CarrierRankGlobal.enumeration datums
      matrix entries fun first second =>
        decide (first.1.key = second.1.key) := by
  unfold sameKeyBits combined
  change pairwise .conjunction
      (indexEqualityBits (PeriodicCNF.numericRouteDescriptors formula))
      (translationEqualityBits
        (PeriodicCNF.numericRouteDescriptors formula)) = _
  rw [indexEqualityBits_numericRouteDescriptors
      formula wellFormed degree isLocal forward nonempty,
    translationEqualityBits_numericRouteDescriptors
      formula wellFormed degree isLocal forward nonempty,
    pairwise_matrix]
  unfold matrix matrixRows
  apply List.flatMap_congr
  intro first _firstMember
  apply List.map_congr_left
  intro second _secondMember
  change
    (decide ((first.1.key.1, first.1.key.2.1) =
        (second.1.key.1, second.1.key.2.1)) &&
      decide (first.1.key.2.2 = second.1.key.2.2)) = _
  exact CarrierRankKeyEquality.decide_carrierKey_eq
    first.1.key second.1.key

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing
