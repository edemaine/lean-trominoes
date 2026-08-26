/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeRankDatumUnaryInjectivity
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeRankDatumUnaryLength
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCompiledRankOrderedFieldNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPairCrossoverData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPairFieldBitNumericSemantics
import LeanTrominoes.UnaryFieldEqualityRowsCompiler

/-! # Numeric semantics of rank-ordered carrier-pair crossover tests -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

open CarrierRankDatumCompiledFields
open SignedUnaryStrictLower

private def fieldValuesEqual (field : Field) :
    List Field → CarrierNodeRankDatum → CarrierNodeRankDatum → Bool
  | [], first, second =>
      decide (first.scanUnaryFields.getD field.index 0 =
        second.scanUnaryFields.getD field.index 0)
  | next :: rest, first, second =>
      decide (first.scanUnaryFields.getD field.index 0 =
        second.scanUnaryFields.getD field.index 0) &&
      fieldValuesEqual next rest first second

private theorem fieldEqualityBits_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (field : Field)
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    fieldEqualityBits field
        (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize descriptors) descriptors).dedup
      let entries := CarrierRankGlobal.enumeration datums
      matrix entries fun first second =>
        decide (first.1.scanUnaryFields.getD field.index 0 =
          second.1.scanUnaryFields.getD field.index 0) := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let datums :=
    (routeDescriptorCarrierRankDatumsAtPeriod
      (routeDescriptorStreamGridSize descriptors) descriptors).dedup
  let entries := CarrierRankGlobal.enumeration datums
  have valuesEq := field.rankOrderedValues_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty
  change field.rankOrderedValues descriptors =
    entries.map fun entry =>
      entry.1.scanUnaryFields.getD field.index 0 at valuesEq
  unfold fieldEqualityBits
  rw [valuesEq, UnaryFieldEqualityRows.equalityBits_eq_flatMap]
  unfold matrix matrixRows
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro first _firstMember
  rw [List.map_map]
  rfl

private theorem fieldEqualityConjunction_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (field : Field) (rest : List Field)
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    fieldEqualityConjunction field rest
        (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize descriptors) descriptors).dedup
      let entries := CarrierRankGlobal.enumeration datums
      matrix entries fun first second =>
        fieldValuesEqual field rest first.1 second.1 := by
  induction rest generalizing field with
  | nil =>
      exact fieldEqualityBits_numericRouteDescriptors field
        formula wellFormed degree isLocal forward nonempty
  | cons next rest induction =>
      unfold fieldEqualityConjunction combined
      change pairwise .conjunction
        (fieldEqualityBits field
          (PeriodicCNF.numericRouteDescriptors formula))
        (fieldEqualityConjunction next rest
          (PeriodicCNF.numericRouteDescriptors formula)) = _
      rw [fieldEqualityBits_numericRouteDescriptors field
          formula wellFormed degree isLocal forward nonempty,
        induction next, pairwise_matrix]
      rfl

private theorem scanUnaryFields_getD_crossingPayload
    (datum : CarrierNodeRankDatum) (code : CrossingRecordCode)
    (crossingEq : datum.boundaryCrossing = some code)
    (index : Nat) (indexLt : index < 32) :
    datum.scanUnaryFields.getD (14 + index) 0 =
      code.scanUnaryFields.getD index 0 := by
  let scanPrefix : List Nat :=
    carrierKeyUnaryFields datum.key ++
      signedUnaryFields datum.orderCoordinate ++
      [if datum.horizontal then 1 else 0] ++
      cellUnaryFields datum.normalizationOffset ++ [1]
  unfold CarrierNodeRankDatum.scanUnaryFields
    CarrierNodeRankDatum.scanDatum CarrierRankScanDatum.unaryFields
  rw [crossingEq]
  change (scanPrefix ++ code.scanUnaryFields ++
      cellUnaryFields datum.ownershipShift).getD (14 + index) 0 = _
  rw [List.append_assoc,
    List.getD_append_right scanPrefix _ 0 (14 + index)
      (by simp [scanPrefix]),
    show 14 + index - scanPrefix.length = index by simp [scanPrefix],
    List.getD_append code.scanUnaryFields _ 0 index
      (by simpa using indexLt)]

private theorem fieldValuesEqual_eq_all
    (field : Field) (rest : List Field)
    (first second : CarrierNodeRankDatum) :
    fieldValuesEqual field rest first second =
      (field :: rest).all fun current =>
        decide (first.scanUnaryFields.getD current.index 0 =
          second.scanUnaryFields.getD current.index 0) := by
  induction rest generalizing field with
  | nil => simp [fieldValuesEqual]
  | cons next rest induction =>
      simp [fieldValuesEqual, induction]

private theorem crossingPayloadFieldIndices :
    (.crossingFirstRoute :: crossingPayloadTail).map Field.index =
      List.range' 14 32 := by
  native_decide

private theorem fieldValuesEqual_crossingPayload
    (first second : CarrierNodeRankDatum)
    (firstCode secondCode : CrossingRecordCode)
    (firstCrossingEq : first.boundaryCrossing = some firstCode)
    (secondCrossingEq : second.boundaryCrossing = some secondCode) :
    fieldValuesEqual .crossingFirstRoute crossingPayloadTail first second =
      decide (firstCode = secondCode) := by
  rw [fieldValuesEqual_eq_all]
  calc
    ((.crossingFirstRoute :: crossingPayloadTail).all fun field =>
        decide (first.scanUnaryFields.getD field.index 0 =
          second.scanUnaryFields.getD field.index 0)) =
        (((.crossingFirstRoute :: crossingPayloadTail).map Field.index).all
          fun index =>
            decide (first.scanUnaryFields.getD index 0 =
              second.scanUnaryFields.getD index 0)) := by
      rw [List.all_map]
      rfl
    _ = (List.range' 14 32).all (fun index =>
          decide (first.scanUnaryFields.getD index 0 =
            second.scanUnaryFields.getD index 0)) := by
      rw [crossingPayloadFieldIndices]
    _ = decide (firstCode = secondCode) := by
      apply Bool.eq_iff_iff.mpr
      rw [List.all_eq_true, decide_eq_true_eq]
      constructor
      · intro fieldsEqual
        apply CrossingRecordCode.scanUnaryFields_injective
        apply List.ext_getElem (by simp)
        intro index firstIndexLt secondIndexLt
        have fullIndexMember : 14 + index ∈ List.range' 14 32 :=
          List.mem_range'.mpr
            ⟨index, by simpa using firstIndexLt, by omega⟩
        have fieldEq := fieldsEqual (14 + index) fullIndexMember
        simp only [decide_eq_true_eq] at fieldEq
        rw [scanUnaryFields_getD_crossingPayload
            first firstCode firstCrossingEq index
              (by simpa using firstIndexLt),
          scanUnaryFields_getD_crossingPayload
            second secondCode secondCrossingEq index
              (by simpa using secondIndexLt)] at fieldEq
        rw [List.getD_eq_getElem firstCode.scanUnaryFields 0 firstIndexLt,
          List.getD_eq_getElem secondCode.scanUnaryFields 0 secondIndexLt]
          at fieldEq
        exact fieldEq
      · intro codesEq
        subst secondCode
        intro fullIndex fullIndexMember
        rcases List.mem_range'.mp fullIndexMember with
          ⟨index, indexLt, fullIndexEq⟩
        simp only [one_mul] at fullIndexEq
        subst fullIndex
        simp only [decide_eq_true_eq]
        rw [scanUnaryFields_getD_crossingPayload
            first firstCode firstCrossingEq index indexLt,
          scanUnaryFields_getD_crossingPayload
            second firstCode secondCrossingEq index indexLt]

/-- All thirty-two compiled payload equalities exactly compare the complete
crossing identities of two boundary endpoints. -/
theorem crossingPayloadEqualityBits_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    crossingPayloadEqualityBits
        (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize descriptors) descriptors).dedup
      let entries := CarrierRankGlobal.enumeration datums
      matrix entries fun first second =>
        fieldValuesEqual .crossingFirstRoute crossingPayloadTail
          first.1 second.1 := by
  exact fieldEqualityConjunction_numericRouteDescriptors
    .crossingFirstRoute crossingPayloadTail formula
    wellFormed degree isLocal forward nonempty

/-- On numeric routes, the compiled same-crossover matrix is exactly the
datum-level crossover-site predicate. -/
theorem sameCrossoverBits_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    sameCrossoverBits (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize descriptors) descriptors).dedup
      let entries := CarrierRankGlobal.enumeration datums
      matrix entries fun first second =>
        first.1.sameCrossoverSite second.1 := by
  unfold sameCrossoverBits combined
  change pairwise .conjunction
      (pairwise .conjunction
        (firstBoundaryBits (PeriodicCNF.numericRouteDescriptors formula))
        (secondBoundaryBits (PeriodicCNF.numericRouteDescriptors formula)))
      (crossingPayloadEqualityBits
        (PeriodicCNF.numericRouteDescriptors formula)) = _
  rw [firstBoundaryBits_numericRouteDescriptors
      formula wellFormed degree isLocal forward nonempty,
    secondBoundaryBits_numericRouteDescriptors
      formula wellFormed degree isLocal forward nonempty,
    crossingPayloadEqualityBits_numericRouteDescriptors
      formula wellFormed degree isLocal forward nonempty,
    pairwise_matrix, pairwise_matrix]
  unfold matrix matrixRows
  apply List.flatMap_congr
  intro first _firstMember
  apply List.map_congr_left
  intro second _secondMember
  cases firstCrossingEq : first.1.boundaryCrossing with
  | none =>
      simp [CarrierNodeRankDatum.sameCrossoverSite,
        firstCrossingEq, UnarySmallSumBooleans.Operation.apply]
  | some firstCode =>
      cases secondCrossingEq : second.1.boundaryCrossing with
      | none =>
          simp [CarrierNodeRankDatum.sameCrossoverSite,
            firstCrossingEq, secondCrossingEq,
            UnarySmallSumBooleans.Operation.apply]
      | some secondCode =>
          simp only [firstCrossingEq, secondCrossingEq,
            CarrierNodeRankDatum.sameCrossoverSite,
            UnarySmallSumBooleans.Operation.apply, Option.isSome,
            Bool.true_and]
          rw [fieldValuesEqual_crossingPayload
            first.1 second.1 firstCode secondCode
            firstCrossingEq secondCrossingEq]

/-- Negating the compiled same-crossover matrix exactly implements the
crossover-suppression predicate. -/
theorem differentCrossoverBits_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    differentCrossoverBits (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize descriptors) descriptors).dedup
      let entries := CarrierRankGlobal.enumeration datums
      matrix entries fun first second =>
        !first.1.sameCrossoverSite second.1 := by
  unfold differentCrossoverBits
  rw [sameCrossoverBits_numericRouteDescriptors
      formula wellFormed degree isLocal forward nonempty,
    negated_matrix]

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing
