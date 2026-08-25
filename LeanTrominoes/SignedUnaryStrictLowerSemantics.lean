/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SignedUnaryStrictLowerCompiler
import LeanTrominoes.UnaryFieldPairPresenceSemantics

/-! # Semantics of signed unary strict comparison -/

namespace LeanTrominoes
namespace SignedUnaryStrictLower

variable {Value : Type*}

def matrixRows (all rows : List Value)
    (predicate : Value → Value → Bool) : List Bool :=
  rows.flatMap fun first => all.map (predicate first)

def matrix (values : List Value)
    (predicate : Value → Value → Bool) : List Bool :=
  matrixRows values values predicate

theorem zipWith_map_same (operation : Bool → Bool → Bool)
    (first second : Value → Bool) (values : List Value) :
    List.zipWith operation (values.map first) (values.map second) =
      values.map fun value => operation (first value) (second value) := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      simp [induction]

theorem zipWith_append_of_length_eq
    (operation : Bool → Bool → Bool)
    (firstPrefix secondPrefix firstSuffix secondSuffix : List Bool)
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

theorem pairwise_matrixRows
    (operation : UnarySmallSumBooleans.Operation)
    (all rows : List Value)
    (first second : Value → Value → Bool) :
    pairwise operation
        (matrixRows all rows first) (matrixRows all rows second) =
      matrixRows all rows fun row column =>
        operation.apply (first row column) (second row column) := by
  induction rows with
  | nil => rfl
  | cons row rows induction =>
      simp only [matrixRows, List.flatMap_cons]
      unfold pairwise
      rw [zipWith_append_of_length_eq _ _ _ _ _ (by simp),
        zipWith_map_same]
      congr 1

theorem pairwise_matrix
    (operation : UnarySmallSumBooleans.Operation)
    (values : List Value)
    (first second : Value → Value → Bool) :
    pairwise operation
        (matrix values first) (matrix values second) =
      matrix values fun row column =>
        operation.apply (first row column) (second row column) :=
  pairwise_matrixRows operation values values first second

theorem negated_matrix (values : List Value)
    (predicate : Value → Value → Bool) :
    AlignedBooleanListClosure.negated (matrix values predicate) =
      matrix values fun first second => !predicate first second := by
  unfold AlignedBooleanListClosure.negated matrix matrixRows
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro value _valueMember
  simp [List.map_map]

def positiveMagnitude (value : Int) : Nat := value.toNat

def negativeMagnitude (value : Int) : Nat := (-value).toNat

theorem positiveLower_magnitudes (values : List Int) :
    positiveLower (values.map positiveMagnitude) =
      matrix values fun first second =>
        decide (positiveMagnitude second < positiveMagnitude first) := by
  unfold positiveLower
  rw [UnaryFieldStrictLowerRows.strictLowerBits_eq_flatMap]
  unfold matrix matrixRows
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro first _firstMember
  simp [List.map_map]

theorem negativeUpper_magnitudes (values : List Int) :
    negativeUpper (values.map negativeMagnitude) =
      matrix values fun first second =>
        decide (negativeMagnitude first < negativeMagnitude second) := by
  unfold negativeUpper
  rw [UnaryFieldStrictLowerRows.strictUpperBits_eq_flatMap]
  unfold matrix matrixRows
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro first _firstMember
  simp [List.map_map]

theorem firstNegative_magnitudes (values : List Int) :
    firstNegative (values.map negativeMagnitude) =
      matrix values fun first _second =>
        decide (0 < negativeMagnitude first) := by
  unfold firstNegative
  rw [UnaryFieldPairPresence.fieldBits_eq_flatMap]
  unfold matrix matrixRows
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro first _firstMember
  simp [List.map_map, Function.comp_def,
    UnaryFieldPairPresence.valuePresent]

theorem secondNegative_magnitudes (values : List Int) :
    secondNegative (values.map negativeMagnitude) =
      matrix values fun _first second =>
        decide (0 < negativeMagnitude second) := by
  unfold secondNegative
  rw [UnaryFieldPairPresence.fieldBits_eq_flatMap]
  unfold matrix matrixRows
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro first _firstMember
  simp [List.map_map, Function.comp_def,
    UnaryFieldPairPresence.valuePresent]

def pairPredicate (first second : Int) : Bool :=
  let firstNegative := decide (0 < negativeMagnitude first)
  let secondNegative := decide (0 < negativeMagnitude second)
  let positiveLower :=
    decide (positiveMagnitude second < positiveMagnitude first)
  let negativeUpper :=
    decide (negativeMagnitude first < negativeMagnitude second)
  ((!firstNegative) && (secondNegative || positiveLower)) ||
    (firstNegative && (secondNegative && negativeUpper))

theorem strictLowerBits_magnitudes_eq_matrix (values : List Int) :
    strictLowerBits
        (values.map positiveMagnitude)
        (values.map negativeMagnitude) =
      matrix values pairPredicate := by
  unfold strictLowerBits nonnegativeCase negativeCase
  rw [positiveLower_magnitudes, negativeUpper_magnitudes,
    firstNegative_magnitudes, secondNegative_magnitudes,
    negated_matrix]
  rw [pairwise_matrix, pairwise_matrix, pairwise_matrix,
    pairwise_matrix, pairwise_matrix]
  rfl

theorem pairPredicate_eq (first second : Int) :
    pairPredicate first second = decide (second < first) := by
  cases first <;> cases second <;>
    simp [pairPredicate, positiveMagnitude, negativeMagnitude] <;> omega

/-- Canonical signed unary magnitudes produce the exact row-major strict-order
matrix on the represented integers. -/
theorem strictLowerBits_magnitudes (values : List Int) :
    strictLowerBits
        (values.map positiveMagnitude)
        (values.map negativeMagnitude) =
      values.flatMap fun first =>
        values.map fun second => decide (second < first) := by
  rw [strictLowerBits_magnitudes_eq_matrix]
  unfold matrix matrixRows
  apply List.flatMap_congr
  intro first _firstMember
  apply List.map_congr_left
  intro second _secondMember
  exact pairPredicate_eq first second

end SignedUnaryStrictLower
end LeanTrominoes
