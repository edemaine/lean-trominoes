/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankCompiledKeyData
import LeanTrominoes.SignedUnaryStrictLowerSemantics

/-! # Proof-free semantics of compiled carrier-key equality -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeyEquality

open SignedUnaryStrictLower

private theorem unaryEqualityBits_field_eq_matrix
    (field : CarrierKeyFieldProjector.Field)
    (descriptors : List RouteDescriptor) :
    UnaryFieldEqualityRows.equalityBits
        (CarrierRankKeyField.values field descriptors) =
      matrix (CarrierRankCompiledKey.values descriptors) fun first second =>
        decide (CarrierRankCompiledKey.fieldValue field first =
          CarrierRankCompiledKey.fieldValue field second) := by
  rw [← CarrierRankCompiledKey.values_map_fieldValue field descriptors,
    UnaryFieldEqualityRows.equalityBits_eq_flatMap]
  unfold matrix matrixRows
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro first _firstMember
  rw [List.map_map]
  rfl

theorem fieldBits_eq_compiledKeyMatrix
    (field : CarrierKeyFieldProjector.Field)
    (descriptors : List RouteDescriptor) :
    fieldBits field descriptors =
      matrix (CarrierRankCompiledKey.values descriptors) fun first second =>
        decide (CarrierRankCompiledKey.fieldValue field first =
          CarrierRankCompiledKey.fieldValue field second) := by
  exact unaryEqualityBits_field_eq_matrix field descriptors

theorem horizontalBits_eq_compiledKeyMatrix
    (descriptors : List RouteDescriptor) :
    horizontalBits descriptors =
      matrix (CarrierRankCompiledKey.values descriptors) fun first second =>
        decide (first.horizontalPositive = second.horizontalPositive) &&
          decide (first.horizontalNegative = second.horizontalNegative) := by
  unfold horizontalBits SignedUnaryEquality.equalityBits
  change pairwise .conjunction
    (UnaryFieldEqualityRows.equalityBits
      (CarrierRankKeyField.values .horizontalPositive descriptors))
    (UnaryFieldEqualityRows.equalityBits
      (CarrierRankKeyField.values .horizontalNegative descriptors)) = _
  rw [unaryEqualityBits_field_eq_matrix .horizontalPositive,
    unaryEqualityBits_field_eq_matrix .horizontalNegative,
    pairwise_matrix]
  rfl

theorem verticalBits_eq_compiledKeyMatrix
    (descriptors : List RouteDescriptor) :
    verticalBits descriptors =
      matrix (CarrierRankCompiledKey.values descriptors) fun first second =>
        decide (first.verticalPositive = second.verticalPositive) &&
          decide (first.verticalNegative = second.verticalNegative) := by
  unfold verticalBits SignedUnaryEquality.equalityBits
  change pairwise .conjunction
    (UnaryFieldEqualityRows.equalityBits
      (CarrierRankKeyField.values .verticalPositive descriptors))
    (UnaryFieldEqualityRows.equalityBits
      (CarrierRankKeyField.values .verticalNegative descriptors)) = _
  rw [unaryEqualityBits_field_eq_matrix .verticalPositive,
    unaryEqualityBits_field_eq_matrix .verticalNegative,
    pairwise_matrix]
  rfl

theorem indexBits_eq_compiledKeyMatrix
    (descriptors : List RouteDescriptor) :
    indexBits descriptors =
      matrix (CarrierRankCompiledKey.values descriptors) fun first second =>
        decide (first.route = second.route) &&
          decide (first.segment = second.segment) := by
  unfold indexBits combined
  change pairwise .conjunction
    (fieldBits .route descriptors) (fieldBits .segment descriptors) = _
  rw [fieldBits_eq_compiledKeyMatrix .route,
    fieldBits_eq_compiledKeyMatrix .segment, pairwise_matrix]
  rfl

theorem translationBits_eq_compiledKeyMatrix
    (descriptors : List RouteDescriptor) :
    translationBits descriptors =
      matrix (CarrierRankCompiledKey.values descriptors) fun first second =>
        (decide (first.horizontalPositive = second.horizontalPositive) &&
          decide (first.horizontalNegative = second.horizontalNegative)) &&
        (decide (first.verticalPositive = second.verticalPositive) &&
          decide (first.verticalNegative = second.verticalNegative)) := by
  unfold translationBits combined
  change pairwise .conjunction
    (horizontalBits descriptors) (verticalBits descriptors) = _
  rw [horizontalBits_eq_compiledKeyMatrix,
    verticalBits_eq_compiledKeyMatrix, pairwise_matrix]
  rfl

theorem bits_eq_compiledKeyMatrix
    (descriptors : List RouteDescriptor) :
    bits descriptors =
      matrix (CarrierRankCompiledKey.values descriptors) fun first second =>
        (decide (first.route = second.route) &&
          decide (first.segment = second.segment)) &&
        ((decide (first.horizontalPositive = second.horizontalPositive) &&
            decide (first.horizontalNegative = second.horizontalNegative)) &&
          (decide (first.verticalPositive = second.verticalPositive) &&
            decide (first.verticalNegative = second.verticalNegative))) := by
  unfold bits combined
  change pairwise .conjunction
    (indexBits descriptors) (translationBits descriptors) = _
  rw [indexBits_eq_compiledKeyMatrix,
    translationBits_eq_compiledKeyMatrix, pairwise_matrix]
  rfl

/-- For every descriptor stream, without route-validity assumptions, the
compiled square is precisely equality on the bundled compiler columns. -/
theorem bits_eq_compiledKeyEqualityRows
    (descriptors : List RouteDescriptor) :
    bits descriptors =
      (CarrierRankCompiledKey.values descriptors).flatMap fun first =>
        (CarrierRankCompiledKey.values descriptors).map fun second =>
          decide (first = second) := by
  rw [bits_eq_compiledKeyMatrix]
  unfold matrix matrixRows
  apply List.flatMap_congr
  intro first _firstMember
  apply List.map_congr_left
  intro second _secondMember
  rcases first with ⟨firstRoute, firstSegment, firstHorizontalPositive,
    firstHorizontalNegative, firstVerticalPositive, firstVerticalNegative⟩
  rcases second with ⟨secondRoute, secondSegment, secondHorizontalPositive,
    secondHorizontalNegative, secondVerticalPositive, secondVerticalNegative⟩
  simp [Bool.and_assoc]

end CarrierRankKeyEquality
end LeanTrominoes.PeriodicOrthocrossing
