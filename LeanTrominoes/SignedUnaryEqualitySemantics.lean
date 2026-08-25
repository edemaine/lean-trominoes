/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SignedUnaryEqualityCompiler
import LeanTrominoes.SignedUnaryStrictLowerSemantics

/-! # Semantics of signed unary equality -/

namespace LeanTrominoes
namespace SignedUnaryEquality

theorem positiveEquality_magnitudes (values : List Int) :
    UnaryFieldEqualityRows.equalityBits
        (values.map SignedUnaryStrictLower.positiveMagnitude) =
      SignedUnaryStrictLower.matrix values fun first second =>
        decide (SignedUnaryStrictLower.positiveMagnitude first =
          SignedUnaryStrictLower.positiveMagnitude second) := by
  rw [UnaryFieldEqualityRows.equalityBits_eq_flatMap]
  unfold SignedUnaryStrictLower.matrix SignedUnaryStrictLower.matrixRows
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro first _firstMember
  simp [List.map_map]

theorem negativeEquality_magnitudes (values : List Int) :
    UnaryFieldEqualityRows.equalityBits
        (values.map SignedUnaryStrictLower.negativeMagnitude) =
      SignedUnaryStrictLower.matrix values fun first second =>
        decide (SignedUnaryStrictLower.negativeMagnitude first =
          SignedUnaryStrictLower.negativeMagnitude second) := by
  rw [UnaryFieldEqualityRows.equalityBits_eq_flatMap]
  unfold SignedUnaryStrictLower.matrix SignedUnaryStrictLower.matrixRows
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro first _firstMember
  simp [List.map_map]

theorem magnitudeEquality_eq (first second : Int) :
    (decide (SignedUnaryStrictLower.positiveMagnitude first =
        SignedUnaryStrictLower.positiveMagnitude second) &&
      decide (SignedUnaryStrictLower.negativeMagnitude first =
        SignedUnaryStrictLower.negativeMagnitude second)) =
      decide (first = second) := by
  cases first <;> cases second <;>
    simp [SignedUnaryStrictLower.positiveMagnitude,
      SignedUnaryStrictLower.negativeMagnitude]

theorem equalityBits_magnitudes (values : List Int) :
    equalityBits
        (values.map SignedUnaryStrictLower.positiveMagnitude)
        (values.map SignedUnaryStrictLower.negativeMagnitude) =
      values.flatMap fun first =>
        values.map fun second => decide (first = second) := by
  unfold equalityBits
  change SignedUnaryStrictLower.pairwise .conjunction
      (UnaryFieldEqualityRows.equalityBits
        (values.map SignedUnaryStrictLower.positiveMagnitude))
      (UnaryFieldEqualityRows.equalityBits
        (values.map SignedUnaryStrictLower.negativeMagnitude)) = _
  rw [positiveEquality_magnitudes, negativeEquality_magnitudes,
    SignedUnaryStrictLower.pairwise_matrix]
  unfold SignedUnaryStrictLower.matrix
    SignedUnaryStrictLower.matrixRows
  apply List.flatMap_congr
  intro first _firstMember
  apply List.map_congr_left
  intro second _secondMember
  exact magnitudeEquality_eq first second

end SignedUnaryEquality
end LeanTrominoes
