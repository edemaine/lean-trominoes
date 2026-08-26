/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizationOffsetFieldIndexSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCompiledRankOrderedFieldNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPairNextSliceData
import LeanTrominoes.SignedUnaryEqualitySemantics
import LeanTrominoes.SignedUnarySuccessorSemantics

/-! # Numeric semantics of rank-ordered carrier-pair next-slice bits -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

open CarrierRankDatumCompiledFields
open SignedUnaryStrictLower

private theorem rankOrderedNormalizationValues_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (compiledField : CarrierRankDatumCompiledFields.Field)
    (normalizationField : CarrierNormalizationOffsetField.Field)
    (indexEq : compiledField.index =
      CarrierNormalizationOffsetField.index normalizationField)
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    compiledField.rankOrderedValues
        (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize descriptors) descriptors).dedup
      let entries := CarrierRankGlobal.enumeration datums
      entries.map fun entry =>
        CarrierNormalizationOffsetField.rankValue
          normalizationField entry.1 := by
  rw [compiledField.rankOrderedValues_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty]
  apply List.map_congr_left
  intro entry _entryMember
  rw [indexEq,
    CarrierNodeRankDatum.scanUnaryFields_getD_normalizationOffsetField]

private theorem horizontalNextBits_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    horizontalNextBits (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize descriptors) descriptors).dedup
      let entries := CarrierRankGlobal.enumeration datums
      matrix entries fun first second =>
        decide (second.1.normalizationOffset.1 =
          first.1.normalizationOffset.1 + 1) := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let datums :=
    (routeDescriptorCarrierRankDatumsAtPeriod
      (routeDescriptorStreamGridSize descriptors) descriptors).dedup
  let entries := CarrierRankGlobal.enumeration datums
  have positiveEq :=
    rankOrderedNormalizationValues_numericRouteDescriptors
      .normalizationHorizontalPositive .horizontalPositive rfl
      formula wellFormed degree isLocal forward nonempty
  have negativeEq :=
    rankOrderedNormalizationValues_numericRouteDescriptors
      .normalizationHorizontalNegative .horizontalNegative rfl
      formula wellFormed degree isLocal forward nonempty
  unfold horizontalNextBits
  rw [positiveEq, negativeEq]
  simpa [CarrierNormalizationOffsetField.rankValue,
      CarrierNormalizationOffsetField.offsetValue,
      CarrierNormalizationOffsetField.horizontal,
      CarrierNormalizationOffsetField.keepPositive,
      SignedUnaryStrictLower.positiveMagnitude,
      SignedUnaryStrictLower.negativeMagnitude] using
    SignedUnarySuccessor.bits_mapped_magnitudes entries
      (fun entry => entry.1.normalizationOffset.1)

private theorem verticalSameBits_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    verticalSameBits (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize descriptors) descriptors).dedup
      let entries := CarrierRankGlobal.enumeration datums
      matrix entries fun first second =>
        decide (first.1.normalizationOffset.2 =
          second.1.normalizationOffset.2) := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let datums :=
    (routeDescriptorCarrierRankDatumsAtPeriod
      (routeDescriptorStreamGridSize descriptors) descriptors).dedup
  let entries := CarrierRankGlobal.enumeration datums
  have positiveEq :=
    rankOrderedNormalizationValues_numericRouteDescriptors
      .normalizationVerticalPositive .verticalPositive rfl
      formula wellFormed degree isLocal forward nonempty
  have negativeEq :=
    rankOrderedNormalizationValues_numericRouteDescriptors
      .normalizationVerticalNegative .verticalNegative rfl
      formula wellFormed degree isLocal forward nonempty
  unfold verticalSameBits
  rw [positiveEq, negativeEq]
  simpa [CarrierNormalizationOffsetField.rankValue,
      CarrierNormalizationOffsetField.offsetValue,
      CarrierNormalizationOffsetField.horizontal,
      CarrierNormalizationOffsetField.keepPositive,
      SignedUnaryStrictLower.positiveMagnitude,
      SignedUnaryStrictLower.negativeMagnitude] using
    SignedUnaryEquality.equalityBits_mapped_magnitudes entries
      (fun entry => entry.1.normalizationOffset.2)

/-- On numeric routes, the compiled offset test is exactly the datum-level
next-slice predicate. -/
theorem nextSliceBits_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    nextSliceBits (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize descriptors) descriptors).dedup
      let entries := CarrierRankGlobal.enumeration datums
      matrix entries fun first second =>
        first.1.pairNextSlice second.1 := by
  unfold nextSliceBits combined
  change pairwise .conjunction
      (horizontalNextBits (PeriodicCNF.numericRouteDescriptors formula))
      (verticalSameBits (PeriodicCNF.numericRouteDescriptors formula)) = _
  rw [horizontalNextBits_numericRouteDescriptors
      formula wellFormed degree isLocal forward nonempty,
    verticalSameBits_numericRouteDescriptors
      formula wellFormed degree isLocal forward nonempty,
    pairwise_matrix]
  unfold matrix matrixRows
  apply List.flatMap_congr
  intro first _firstMember
  apply List.map_congr_left
  intro second _secondMember
  apply Bool.eq_iff_iff.mpr
  simp only [UnarySmallSumBooleans.Operation.apply, Bool.and_eq_true,
    decide_eq_true_eq, CarrierNodeRankDatum.pairNextSlice, Cell.sub,
    Prod.mk.injEq]
  omega

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing
