/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedRetainedPairData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedRetainedPairMaskNumericSemantics
import LeanTrominoes.UnaryAlignedAddSemantics

/-! # Numeric semantics of sparse globally rank-ordered retained pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

open SignedUnaryStrictLower

private def matrixOf {Value Output : Type*} (values : List Value)
    (function : Value → Value → Output) : List Output :=
  values.flatMap fun first => values.map (function first)

private theorem map_matrix
    {Value First Second : Type*}
    (values : List Value) (function : First → Second)
    (predicate : Value → Value → First) :
    (matrixOf values predicate).map function =
      matrixOf values fun first second => function (predicate first second) := by
  unfold matrixOf
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro first _firstMember
  simp [List.map_map]

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

private theorem added_matrix {Value : Type*}
    (values : List Value)
    (first second : Value → Value → Nat) :
    AlignedUnaryListClosure.added
        (matrixOf values first) (matrixOf values second) =
      matrixOf values fun row column => first row column + second row column := by
  unfold AlignedUnaryListClosure.added
  rw [UnaryAlignedAddMachine.sums_eq_zipWith
    (UnaryAlignedAddMachine.Valid.of_length_eq (by simp [matrixOf]))]
  exact zipWith_matrix (· + ·) values first second

private def emissionCode (mask axis nextSlice : Bool) : Nat :=
  (BooleanListUnaryFields.bitNat mask +
      BooleanListUnaryFields.bitNat (mask && axis)) +
    (BooleanListUnaryFields.bitNat (mask && nextSlice) +
      BooleanListUnaryFields.bitNat (mask && nextSlice))

private theorem pair?_emissionCode (mask axis nextSlice : Bool) :
    UnaryCarrierPairBits.pair? (emissionCode mask axis nextSlice) =
      if mask then some (axis, nextSlice) else none := by
  cases mask <;> cases axis <;> cases nextSlice <;> rfl

/-- The three aligned Boolean streams become zero for rejected pairs and
codes one through four for the four retained metadata combinations. -/
theorem emissionCodes_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    emissionCodes (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize descriptors) descriptors).dedup
      let entries := CarrierRankGlobal.enumeration datums
      matrixOf entries.zipIdx fun first second =>
        emissionCode
          (retainedPredicate first second)
          first.1.1.horizontal
          (first.1.1.pairNextSlice second.1.1) := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let datums :=
    (routeDescriptorCarrierRankDatumsAtPeriod
      (routeDescriptorStreamGridSize descriptors) descriptors).dedup
  let entries := CarrierRankGlobal.enumeration datums
  have maskEq := retainedMaskBits_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty
  change retainedMaskBits descriptors =
    matrixOf entries.zipIdx retainedPredicate at maskEq
  have axisEq := retainedAxisBits_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty
  change retainedAxisBits descriptors =
    matrixOf entries.zipIdx fun first second =>
      retainedPredicate first second && first.1.1.horizontal at axisEq
  have nextEq := retainedNextSliceBits_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty
  change retainedNextSliceBits descriptors =
    matrixOf entries.zipIdx fun first second =>
      retainedPredicate first second &&
        first.1.1.pairNextSlice second.1.1 at nextEq
  unfold emissionCodes baseEmissionCodes doubledNextSliceCodes
  rw [maskEq, axisEq, nextEq]
  unfold BooleanListUnaryFields.values
  rw [map_matrix, map_matrix, map_matrix]
  rw [added_matrix, added_matrix, added_matrix]
  rfl

private theorem filterMap_flatMap
    {First Second Result : Type*}
    (values : List First) (row : First → List Second)
    (function : Second → Option Result) :
    (values.flatMap row).filterMap function =
      values.flatMap fun value => (row value).filterMap function := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      simp [List.filterMap_append, induction]

/-- The decoded sparse output is exactly the row-major selected-pair
metadata stream. -/
theorem retainedPairBits_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    retainedPairBits (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize descriptors) descriptors).dedup
      let entries := CarrierRankGlobal.enumeration datums
      entries.zipIdx.flatMap fun first =>
        entries.zipIdx.filterMap fun second =>
          if retainedPredicate first second then
            some
              (first.1.1.horizontal,
                first.1.1.pairNextSlice second.1.1)
          else
            none := by
  unfold retainedPairBits UnaryCarrierPairBits.pairs
  rw [emissionCodes_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty]
  unfold matrixOf
  rw [filterMap_flatMap]
  apply List.flatMap_congr
  intro first _firstMember
  rw [List.filterMap_map]
  apply List.filterMap_congr
  intro second _secondMember
  simp only [Function.comp_apply, pair?_emissionCode]

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing
