/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedMaskedSpanNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedTaggedSpanData
import LeanTrominoes.UnaryAlignedAddSemantics

/-! # Numeric semantics of axis-tagged retained carrier spans -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

private def matrixOf {Value Output : Type*} (values : List Value)
    (function : Value → Value → Output) : List Output :=
  values.flatMap fun first => values.map (function first)

private theorem matrixOf_zipIdx_fst
    {Value Output : Type*} (values : List Value)
    (function : Value → Value → Output) :
    matrixOf values function =
      matrixOf values.zipIdx fun first second =>
        function first.1 second.1 := by
  unfold matrixOf
  conv_lhs =>
    rw [← List.zipIdx_map_fst 0 values]
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro first _firstMember
  rw [List.map_map]
  rfl

private theorem zipWith_map_same
    {Value First Second Result : Type*}
    (operation : First → Second → Result)
    (first : Value → First) (second : Value → Second)
    (values : List Value) :
    List.zipWith operation (values.map first) (values.map second) =
      values.map fun value => operation (first value) (second value) := by
  induction values with
  | nil => rfl
  | cons value values induction => simp [induction]

private theorem zipWith_append_of_length_eq
    {First Second Result : Type*}
    (operation : First → Second → Result)
    (firstPrefix firstSuffix : List First)
    (secondPrefix secondSuffix : List Second)
    (lengthEq : firstPrefix.length = secondPrefix.length) :
    List.zipWith operation
        (firstPrefix ++ firstSuffix) (secondPrefix ++ secondSuffix) =
      List.zipWith operation firstPrefix secondPrefix ++
        List.zipWith operation firstSuffix secondSuffix := by
  induction firstPrefix generalizing secondPrefix with
  | nil =>
      have secondNil : secondPrefix = [] :=
        List.eq_nil_of_length_eq_zero (by simpa using lengthEq.symm)
      subst secondPrefix
      rfl
  | cons first firstPrefix induction =>
      cases secondPrefix with
      | nil => simp at lengthEq
      | cons second secondPrefix =>
          simp only [List.length_cons] at lengthEq
          simp [induction secondPrefix (by omega)]

private theorem zipWith_matrixRows
    {Value First Second Result : Type*}
    (operation : First → Second → Result)
    (all rows : List Value)
    (first : Value → Value → First)
    (second : Value → Value → Second) :
    List.zipWith operation
        (rows.flatMap fun row => all.map (first row))
        (rows.flatMap fun row => all.map (second row)) =
      rows.flatMap fun row => all.map fun column =>
        operation (first row column) (second row column) := by
  induction rows with
  | nil => rfl
  | cons row rows induction =>
      simp only [List.flatMap_cons]
      rw [zipWith_append_of_length_eq operation _ _ _ _ (by simp),
        zipWith_map_same, induction]

private theorem zipWith_matrix
    {Value First Second Result : Type*}
    (operation : First → Second → Result)
    (values : List Value)
    (first : Value → Value → First)
    (second : Value → Value → Second) :
    List.zipWith operation
        (matrixOf values first) (matrixOf values second) =
      matrixOf values fun row column =>
        operation (first row column) (second row column) :=
  zipWith_matrixRows operation values values first second

private theorem map_matrix
    {Value First Second : Type*}
    (values : List Value) (function : First → Second)
    (source : Value → Value → First) :
    (matrixOf values source).map function =
      matrixOf values fun first second => function (source first second) := by
  unfold matrixOf
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro first _firstMember
  simp [List.map_map]

private theorem added_eq_zipWith (first second : List Nat)
    (lengthEq : first.length = second.length) :
    AlignedUnaryListClosure.added first second =
      List.zipWith (· + ·) first second := by
  unfold AlignedUnaryListClosure.added
  exact UnaryAlignedAddMachine.sums_eq_zipWith
    (UnaryAlignedAddMachine.Valid.of_length_eq lengthEq)

theorem taggedSpanCodes_eq_zipWith (descriptors : List RouteDescriptor) :
    taggedSpanCodes descriptors =
      List.zipWith (· + ·)
        (List.zipWith
          (fun doubled active => if active then doubled + 2 else 0)
          (List.zipWith (· + ·)
            (orderSpans descriptors) (orderSpans descriptors))
          (retainedMaskBits descriptors))
        (BooleanListUnaryFields.values
          (retainedAxisBits descriptors)) := by
  unfold taggedSpanCodes maskedDoubledSpanCodes doubledOrderSpans
  rw [added_eq_zipWith _ _ (by
      unfold maskedSpanCodes
      rw [selectedValues_length]
      simp [BooleanListUnaryFields.values]),
    maskedSpanCodes_eq_zipWith _ _ (by simp),
    added_eq_zipWith _ _ rfl]

/-- Numeric tagged fields preserve global pair order, suppress rejected
pairs, and encode retained vertical/horizontal spans as `2s+2`/`2s+3`. -/
theorem taggedSpanCodes_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    taggedSpanCodes (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize descriptors) descriptors).dedup
      let entries := CarrierRankGlobal.enumeration datums
      matrixOf entries.zipIdx fun first second =>
        if retainedPredicate first second then
          let span := (second.1.1.orderCoordinate -
            first.1.1.orderCoordinate).toNat
          span + span + 2 +
            BooleanListUnaryFields.bitNat first.1.1.horizontal
        else 0 := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let datums :=
    (routeDescriptorCarrierRankDatumsAtPeriod
      (routeDescriptorStreamGridSize descriptors) descriptors).dedup
  let entries := CarrierRankGlobal.enumeration datums
  have spanEq := orderSpans_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty
  change orderSpans descriptors =
    matrixOf entries fun first second =>
      (second.1.orderCoordinate - first.1.orderCoordinate).toNat at spanEq
  rw [matrixOf_zipIdx_fst entries
    (fun first second =>
      (second.1.orderCoordinate - first.1.orderCoordinate).toNat)] at spanEq
  have maskEq := retainedMaskBits_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty
  change retainedMaskBits descriptors =
    matrixOf entries.zipIdx retainedPredicate at maskEq
  have axisEq := retainedAxisBits_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty
  change retainedAxisBits descriptors =
    matrixOf entries.zipIdx fun first second =>
      retainedPredicate first second && first.1.1.horizontal at axisEq
  rw [taggedSpanCodes_eq_zipWith, spanEq, maskEq, axisEq,
    zipWith_matrix, zipWith_matrix]
  unfold BooleanListUnaryFields.values
  rw [map_matrix, zipWith_matrix]
  unfold matrixOf
  apply List.flatMap_congr
  intro first _firstMember
  apply List.map_congr_left
  intro second _secondMember
  cases retained : retainedPredicate first second <;>
    cases horizontal : first.1.1.horizontal <;>
      simp [retained, horizontal, BooleanListUnaryFields.bitNat]

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing
