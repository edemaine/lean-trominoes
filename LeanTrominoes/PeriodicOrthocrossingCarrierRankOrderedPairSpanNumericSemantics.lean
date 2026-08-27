/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCompiledRankOrderedFieldNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPairSpanData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderFieldIndexSemantics
import LeanTrominoes.UnaryAlignedAddSemantics

/-! # Numeric semantics of rank-ordered carrier-coordinate spans -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

open CarrierRankDatumCompiledFields

private def matrixOf {Value Output : Type*} (values : List Value)
    (function : Value → Value → Output) : List Output :=
  values.flatMap fun first => values.map (function first)

private theorem matrixOf_map
    {Value Measure Output : Type*}
    (values : List Value) (measure : Value → Measure)
    (function : Measure → Measure → Output) :
    matrixOf (values.map measure) function =
      matrixOf values fun first second =>
        function (measure first) (measure second) := by
  unfold matrixOf
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro first _firstMember
  simp [List.map_map]

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

private theorem added_matrix {Value : Type*}
    (values : List Value)
    (first second : Value → Value → Nat) :
    AlignedUnaryListClosure.added
        (matrixOf values first) (matrixOf values second) =
      matrixOf values fun row column => first row column + second row column := by
  unfold AlignedUnaryListClosure.added matrixOf
  rw [UnaryAlignedAddMachine.sums_eq_zipWith
    (UnaryAlignedAddMachine.Valid.of_length_eq (by simp))]
  exact zipWith_matrixRows (· + ·) values values first second

private theorem signedSpan (first second : Int) :
    (second.toNat - first.toNat) +
        ((-first).toNat - (-second).toNat) =
      (second - first).toNat := by
  cases first <;> cases second <;> simp <;> omega

private theorem orderExcesses_eq_matrixOf
    (field : Field) (keepFirst : Bool)
    (descriptors : List RouteDescriptor) :
    orderExcesses field keepFirst descriptors =
      matrixOf (field.rankOrderedValues descriptors) fun first second =>
        if keepFirst then first - second else second - first := by
  unfold orderExcesses orderWordPairs
    DelimitedBinaryWordPairExcessMachine.excesses
    DelimitedBinaryWordPairProductMachine.pairs
    UnaryFieldBinaryWords.words matrixOf
  simp only [List.map_flatMap, List.flatMap_map, List.map_map,
    Function.comp_def]
  apply List.flatMap_congr
  intro first _firstMember
  apply List.map_congr_left
  intro second _secondMember
  simp [DelimitedBinaryWordPairExcessMachine.excess,
    UnaryFieldBinaryWords.word]

/-- On numeric routes, the compiled row-major span is exactly the
nonnegative signed order-coordinate difference of every globally ranked
carrier datum pair. -/
theorem orderSpans_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    orderSpans (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize descriptors) descriptors).dedup
      let entries := CarrierRankGlobal.enumeration datums
      entries.flatMap fun first => entries.map fun second =>
        (second.1.orderCoordinate - first.1.orderCoordinate).toNat := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let datums :=
    (routeDescriptorCarrierRankDatumsAtPeriod
      (routeDescriptorStreamGridSize descriptors) descriptors).dedup
  let entries := CarrierRankGlobal.enumeration datums
  have positiveEq :
      Field.rankOrderedValues .orderPositive descriptors =
        entries.map fun entry => entry.1.orderCoordinate.toNat := by
    rw [Field.rankOrderedValues_numericRouteDescriptors .orderPositive
      formula wellFormed degree isLocal forward nonempty]
    apply List.map_congr_left
    intro entry _entryMember
    exact CarrierNodeRankDatum.scanUnaryFields_getD_six entry.1
  have negativeEq :
      Field.rankOrderedValues .orderNegative descriptors =
        entries.map fun entry => (-entry.1.orderCoordinate).toNat := by
    rw [Field.rankOrderedValues_numericRouteDescriptors .orderNegative
      formula wellFormed degree isLocal forward nonempty]
    apply List.map_congr_left
    intro entry _entryMember
    exact CarrierNodeRankDatum.scanUnaryFields_getD_seven entry.1
  unfold orderSpans
  rw [orderExcesses_eq_matrixOf, orderExcesses_eq_matrixOf,
    positiveEq, negativeEq, matrixOf_map, matrixOf_map, added_matrix]
  unfold matrixOf
  apply List.flatMap_congr
  intro first _firstMember
  apply List.map_congr_left
  intro second _secondMember
  exact signedSpan first.1.orderCoordinate second.1.orderCoordinate

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing
