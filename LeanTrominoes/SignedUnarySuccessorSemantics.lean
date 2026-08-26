/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SignedUnarySuccessorCompiler
import LeanTrominoes.SignedUnaryStrictLowerSemantics
import LeanTrominoes.UnaryFieldPairPresenceSemantics

/-! # Semantics of successor matrices over signed unary values -/

namespace LeanTrominoes

namespace UnaryFieldSuccessorRows

open SignedUnaryStrictLower

/-- Exact-one truncated differences implement the requested orientation of
natural-number succession. -/
theorem bits_eq_matrix (keepFirst : Bool) (values : List Nat) :
    bits keepFirst values =
      matrix values fun first second =>
        decide (if keepFirst then first = second + 1
          else second = first + 1) := by
  unfold bits excesses wordPairs
  rw [UnaryExactOneBooleans.bits_eq_map]
  unfold DelimitedBinaryWordPairExcessMachine.excesses
    DelimitedBinaryWordPairProductMachine.pairs
    UnaryFieldBinaryWords.words matrix matrixRows
  simp only [List.map_flatMap, List.flatMap_map, List.map_map,
    Function.comp_def]
  apply List.flatMap_congr
  intro first _firstMember
  apply List.map_congr_left
  intro second _secondMember
  cases keepFirst <;>
    simp [DelimitedBinaryWordPairExcessMachine.excess,
      UnaryFieldBinaryWords.word] <;> omega

/-- Natural successor rows commute with an arbitrary projection. -/
theorem bits_mapped {Value : Type*} (keepFirst : Bool)
    (values : List Value) (value : Value → Nat) :
    bits keepFirst (values.map value) =
      matrix values fun first second =>
        decide (if keepFirst then value first = value second + 1
          else value second = value first + 1) := by
  simpa [matrix, matrixRows, List.flatMap_map, List.map_map,
      Function.comp_def] using
    bits_eq_matrix keepFirst (values.map value)

end UnaryFieldSuccessorRows

namespace SignedUnarySuccessor

open SignedUnaryStrictLower

/-- Negating row and column positivity tests recognizes two zero
magnitudes. -/
theorem bothZeroBits_eq_matrix (values : List Nat) :
    bothZeroBits values =
      matrix values fun first second =>
        decide (first = 0) && decide (second = 0) := by
  unfold bothZeroBits
  rw [UnaryFieldPairPresence.fieldBits_eq_flatMap,
    UnaryFieldPairPresence.fieldBits_eq_flatMap]
  change pairwise .conjunction
      (AlignedBooleanListClosure.negated
        (matrix values fun first second =>
          UnaryFieldPairPresence.valuePresent .first first second))
      (AlignedBooleanListClosure.negated
        (matrix values fun first second =>
          UnaryFieldPairPresence.valuePresent .second first second)) = _
  rw [negated_matrix, negated_matrix, pairwise_matrix]
  unfold matrix matrixRows
  apply List.flatMap_congr
  intro first _firstMember
  apply List.map_congr_left
  intro second _secondMember
  cases first <;> cases second <;>
    simp [UnarySmallSumBooleans.Operation.apply,
      UnaryFieldPairPresence.valuePresent]

theorem bothZeroBits_mapped {Value : Type*}
    (values : List Value) (value : Value → Nat) :
    bothZeroBits (values.map value) =
      matrix values fun first second =>
        decide (value first = 0) && decide (value second = 0) := by
  simpa [matrix, matrixRows, List.flatMap_map, List.map_map,
      Function.comp_def] using
    bothZeroBits_eq_matrix (values.map value)

private theorem successorPredicate (first second : Int) :
    ((decide (positiveMagnitude second = positiveMagnitude first + 1) &&
        (decide (negativeMagnitude first = 0) &&
          decide (negativeMagnitude second = 0))) ||
      (decide (negativeMagnitude first = negativeMagnitude second + 1) &&
        (decide (positiveMagnitude first = 0) &&
          decide (positiveMagnitude second = 0)))) =
      decide (second = first + 1) := by
  cases first with
  | ofNat first =>
      cases second with
      | ofNat second =>
          simp [positiveMagnitude, negativeMagnitude]
          all_goals omega
      | negSucc second =>
          simp [positiveMagnitude, negativeMagnitude, Int.negSucc_eq]
          all_goals omega
  | negSucc first =>
      cases second with
      | ofNat second =>
          by_cases firstZero : first = 0 <;>
            by_cases secondZero : second = 0 <;>
              simp [positiveMagnitude, negativeMagnitude, Int.negSucc_eq,
                firstZero, secondZero]
      | negSucc second =>
          simp [positiveMagnitude, negativeMagnitude, Int.negSucc_eq]
          all_goals omega

/-- Canonical positive and negative magnitudes produce exactly the
row-major signed successor matrix. -/
theorem bits_magnitudes (values : List Int) :
    bits
        (values.map positiveMagnitude)
        (values.map negativeMagnitude) =
      matrix values fun first second => decide (second = first + 1) := by
  unfold bits nonnegativeCase negativeCase
  rw [UnaryFieldSuccessorRows.bits_mapped false values positiveMagnitude,
    bothZeroBits_mapped values negativeMagnitude,
    UnaryFieldSuccessorRows.bits_mapped true values negativeMagnitude,
    bothZeroBits_mapped values positiveMagnitude,
    pairwise_matrix, pairwise_matrix, pairwise_matrix]
  unfold matrix matrixRows
  apply List.flatMap_congr
  intro first _firstMember
  apply List.map_congr_left
  intro second _secondMember
  exact successorPredicate first second

/-- Signed successor matrices commute with an arbitrary integer
projection. -/
theorem bits_mapped_magnitudes {Value : Type*}
    (values : List Value) (value : Value → Int) :
    bits
        (values.map fun current => positiveMagnitude (value current))
        (values.map fun current => negativeMagnitude (value current)) =
      matrix values fun first second =>
        decide (value second = value first + 1) := by
  simpa [List.map_map, Function.comp_def, matrix, matrixRows,
      List.flatMap_map] using
    bits_magnitudes (values.map value)

end SignedUnarySuccessor
end LeanTrominoes
