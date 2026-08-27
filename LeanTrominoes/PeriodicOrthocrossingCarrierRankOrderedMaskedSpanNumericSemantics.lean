/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedMaskedSpanData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPairSpanNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedRetainedPairMaskNumericSemantics

/-! # Numeric semantics of axis-masked retained carrier spans -/

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
        operation (first row column) (second row column) := by
  exact zipWith_matrixRows operation values values first second

private theorem negated_matrix {Value : Type*} (values : List Value)
    (predicate : Value → Value → Bool) :
    AlignedBooleanListClosure.negated (matrixOf values predicate) =
      matrixOf values fun first second => !predicate first second := by
  unfold AlignedBooleanListClosure.negated matrixOf
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro value _valueMember
  simp [List.map_map]

theorem maskedSpanCodes_eq_zipWith (spans : List Nat) (mask : List Bool)
    (lengthEq : spans.length = mask.length) :
    maskedSpanCodes spans mask =
      List.zipWith (fun span active => if active then span + 2 else 0)
        spans mask := by
  induction spans generalizing mask with
  | nil =>
      have maskNil : mask = [] :=
        List.eq_nil_of_length_eq_zero (by simpa using lengthEq.symm)
      subst mask
      rfl
  | cons span spans induction =>
      cases mask with
      | nil => simp at lengthEq
      | cons active mask =>
          have tailLength : spans.length = mask.length := by
            simpa using lengthEq
          change UnarySuccessorEqualityFilterMachine.selectedValue
                (span + 1)
                (span + 2 + BooleanListUnaryFields.bitNat (!active)) ::
              maskedSpanCodes spans mask =
            (if active then span + 2 else 0) ::
              List.zipWith
                (fun span active => if active then span + 2 else 0)
                spans mask
          rw [induction mask tailLength]
          cases active <;>
            simp [UnarySuccessorEqualityFilterMachine.selectedValue,
              BooleanListUnaryFields.bitNat]

/-- The vertical mask selects exactly retained pairs whose first endpoint is
vertical. -/
theorem verticalMaskBits_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    verticalMaskBits (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize descriptors) descriptors).dedup
      let entries := CarrierRankGlobal.enumeration datums
      matrixOf entries.zipIdx fun first second =>
        retainedPredicate first second && !first.1.1.horizontal := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let datums :=
    (routeDescriptorCarrierRankDatumsAtPeriod
      (routeDescriptorStreamGridSize descriptors) descriptors).dedup
  let entries := CarrierRankGlobal.enumeration datums
  have maskEq := retainedMaskBits_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty
  change retainedMaskBits descriptors =
    matrixOf entries.zipIdx retainedPredicate at maskEq
  have axisEq := axisBits_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty
  change axisBits descriptors =
    matrixOf entries (fun first _second => first.1.horizontal) at axisEq
  rw [matrixOf_zipIdx_fst entries
    (fun first _second => first.1.horizontal)] at axisEq
  unfold verticalMaskBits combined
  rw [maskEq, axisEq, negated_matrix, zipWith_matrix]

theorem horizontalSpanCodes_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    horizontalSpanCodes (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize descriptors) descriptors).dedup
      let entries := CarrierRankGlobal.enumeration datums
      matrixOf entries.zipIdx fun first second =>
        if retainedPredicate first second && first.1.1.horizontal then
          (second.1.1.orderCoordinate -
              first.1.1.orderCoordinate).toNat + 2
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
  have maskEq := retainedAxisBits_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty
  change retainedAxisBits descriptors =
    matrixOf entries.zipIdx fun first second =>
      retainedPredicate first second && first.1.1.horizontal at maskEq
  unfold horizontalSpanCodes
  rw [maskedSpanCodes_eq_zipWith _ _ (by simp), spanEq, maskEq,
    zipWith_matrix]

theorem verticalSpanCodes_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    verticalSpanCodes (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize descriptors) descriptors).dedup
      let entries := CarrierRankGlobal.enumeration datums
      matrixOf entries.zipIdx fun first second =>
        if retainedPredicate first second && !first.1.1.horizontal then
          (second.1.1.orderCoordinate -
              first.1.1.orderCoordinate).toNat + 2
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
  have maskEq := verticalMaskBits_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty
  change verticalMaskBits descriptors =
    matrixOf entries.zipIdx fun first second =>
      retainedPredicate first second && !first.1.1.horizontal at maskEq
  unfold verticalSpanCodes
  rw [maskedSpanCodes_eq_zipWith _ _ (by simp), spanEq, maskEq,
    zipWith_matrix]

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing
