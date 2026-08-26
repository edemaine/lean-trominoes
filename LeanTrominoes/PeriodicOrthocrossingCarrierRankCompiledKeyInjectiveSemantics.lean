/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankCompiledKeyNumericSemantics
import LeanTrominoes.SignedUnaryEqualitySemantics

/-! # Injectivity of aggregate semantic carrier keys -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankCompiledKey

private theorem int_eq_of_magnitudes_eq
    (first second : Int)
    (positive : first.toNat = second.toNat)
    (negative : (-first).toNat = (-second).toNat) :
    first = second := by
  apply of_decide_eq_true
  rw [← SignedUnaryEquality.magnitudeEquality_eq first second]
  simp [SignedUnaryStrictLower.positiveMagnitude,
    SignedUnaryStrictLower.negativeMagnitude, positive, negative]

/-- Canonical positive/negative magnitudes make the six-field aggregate
encoding injective on semantic carrier keys. -/
theorem ofKey_injective : Function.Injective ofKey := by
  intro first second equal
  rcases first with
    ⟨firstRoute, firstSegment, firstHorizontal, firstVertical⟩
  rcases second with
    ⟨secondRoute, secondSegment, secondHorizontal, secondVertical⟩
  have routeEq := congrArg CarrierRankCompiledKey.route equal
  have segmentEq := congrArg CarrierRankCompiledKey.segment equal
  have horizontalPositiveEq :=
    congrArg CarrierRankCompiledKey.horizontalPositive equal
  have horizontalNegativeEq :=
    congrArg CarrierRankCompiledKey.horizontalNegative equal
  have verticalPositiveEq :=
    congrArg CarrierRankCompiledKey.verticalPositive equal
  have verticalNegativeEq :=
    congrArg CarrierRankCompiledKey.verticalNegative equal
  simp only [ofKey] at routeEq
  simp only [ofKey] at segmentEq
  simp only [ofKey] at horizontalPositiveEq
  simp only [ofKey] at horizontalNegativeEq
  simp only [ofKey] at verticalPositiveEq
  simp only [ofKey] at verticalNegativeEq
  have horizontalEq := int_eq_of_magnitudes_eq
    firstHorizontal secondHorizontal
    horizontalPositiveEq horizontalNegativeEq
  have verticalEq := int_eq_of_magnitudes_eq
    firstVertical secondVertical
    verticalPositiveEq verticalNegativeEq
  subst secondRoute
  subst secondSegment
  subst secondHorizontal
  subst secondVertical
  rfl

@[simp] theorem ofKey_inj
    (first second : Nat × Nat × Cell) :
    ofKey first = ofKey second ↔ first = second :=
  ofKey_injective.eq_iff

@[simp] theorem ofDatum_eq_iff_key_eq
    (first second : CarrierNodeRankDatum) :
    ofDatum first = ofDatum second ↔ first.key = second.key := by
  simp [ofDatum]

end CarrierRankCompiledKey
end LeanTrominoes.PeriodicOrthocrossing
