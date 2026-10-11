/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentDirectionPerturbation

/-! # Slope order survives bounded port displacement

Moving each endpoint to a nearby rectangle anchor changes its direction by
a constant amount. A refinement linear in the original direction bound
preserves the strict sign of every nonzero cross product.
-/
namespace LeanTrominoes.GridSegment

def BoundedVectorPerturbation (radius factor : Int) (original output : Cell) : Prop :=
  |output.1-factor*original.1| ≤ radius ∧ |output.2-factor*original.2| ≤ radius

theorem BoundedVectorPerturbation.horizontal_slope_bound {radius factor bound : Int} {original output : Cell}
    (perturbed : BoundedVectorPerturbation radius factor original output)
    (radiusNonnegative : 0 ≤ radius) (boundNonnegative : 0 ≤ bound)
    (spacing : 2*radius < factor) (rightward : 0 < original.1) (verticalBound : |original.2| ≤ bound) :
    0 < output.1 ∧ |output.2| ≤ (2*bound+1)*output.1 := by
  have factorPositive : 0 < factor := by omega
  have rightAtLeastOne : 1 ≤ original.1 := by omega
  have scaledRight := mul_le_mul_of_nonneg_left rightAtLeastOne factorPositive.le
  have lowerX := (abs_le.mp perturbed.1).1
  have outputXLower : factor-radius ≤ output.1 := by nlinarith
  have outputYBound : |output.2| ≤ factor*bound+radius := by
    calc
      _ = |(output.2-factor*original.2)+factor*original.2| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ radius+factor*bound := add_le_add perturbed.2 (by
        rw [abs_mul,abs_of_pos factorPositive]
        exact mul_le_mul_of_nonneg_left verticalBound factorPositive.le)
      _ = _ := by ring
  refine ⟨by omega,?_⟩
  have scaledLower := mul_le_mul_of_nonneg_left outputXLower (by positivity : 0 ≤ 2*bound+1)
  have errorMargin := mul_nonneg (by omega : 0 ≤ factor-2*radius) boundNonnegative
  nlinarith

theorem bounded_product_perturbation {factor bound radius a b outputA outputB : Int}
    (factorNonnegative : 0 ≤ factor) (boundNonnegative : 0 ≤ bound) (radiusNonnegative : 0 ≤ radius)
    (aBound : |a| ≤ bound) (bBound : |b| ≤ bound)
    (aPerturbed : |outputA-factor*a| ≤ radius) (bPerturbed : |outputB-factor*b| ≤ radius) :
    |outputA*outputB-factor*factor*(a*b)| ≤ 2*factor*bound*radius+radius*radius := by
  let ea := outputA-factor*a
  let eb := outputB-factor*b
  have firstBound : |a*eb| ≤ bound*radius := by
    rw [abs_mul]
    exact mul_le_mul aBound bPerturbed (abs_nonneg _) boundNonnegative
  have secondBound : |ea*b| ≤ radius*bound := by
    rw [abs_mul]
    exact mul_le_mul aPerturbed bBound (abs_nonneg _) radiusNonnegative
  have errorBound : |ea*eb| ≤ radius*radius := by
    rw [abs_mul]
    exact mul_le_mul aPerturbed bPerturbed (abs_nonneg _) radiusNonnegative
  calc
    _ = |factor*(a*eb+ea*b)+ea*eb| := by congr 1; dsimp [ea,eb]; ring
    _ ≤ |factor*(a*eb+ea*b)|+|ea*eb| := abs_add_le _ _
    _ = factor*|a*eb+ea*b|+|ea*eb| := by rw [abs_mul,abs_of_nonneg factorNonnegative]
    _ ≤ factor*(|a*eb|+|ea*b|)+radius*radius := add_le_add
      (mul_le_mul_of_nonneg_left (abs_add_le _ _) factorNonnegative) errorBound
    _ ≤ factor*(bound*radius+radius*bound)+radius*radius := add_le_add
      (mul_le_mul_of_nonneg_left (add_le_add firstBound secondBound) factorNonnegative) (le_refl _)
    _ = _ := by ring

theorem bounded_cross_perturbation {factor bound radius : Int}
    (factorNonnegative : 0 ≤ factor) (boundNonnegative : 0 ≤ bound) (radiusNonnegative : 0 ≤ radius)
    {first second firstOut secondOut : Cell}
    (firstBounds : |first.1| ≤ bound ∧ |first.2| ≤ bound)
    (secondBounds : |second.1| ≤ bound ∧ |second.2| ≤ bound)
    (firstPerturbed : BoundedVectorPerturbation radius factor first firstOut)
    (secondPerturbed : BoundedVectorPerturbation radius factor second secondOut) :
    |cross firstOut secondOut-factor*factor*cross first second| ≤
      4*factor*bound*radius+2*radius*radius := by
  have firstBound := bounded_product_perturbation factorNonnegative boundNonnegative radiusNonnegative
    firstBounds.1 secondBounds.2 firstPerturbed.1 secondPerturbed.2
  have secondBound := bounded_product_perturbation factorNonnegative boundNonnegative radiusNonnegative
    firstBounds.2 secondBounds.1 firstPerturbed.2 secondPerturbed.1
  calc
    _ = |(firstOut.1*secondOut.2-factor*factor*(first.1*second.2))-
        (firstOut.2*secondOut.1-factor*factor*(first.2*second.1))| := by congr 1; unfold cross; ring
    _ ≤ _ := abs_sub _ _
    _ ≤ (2*factor*bound*radius+radius*radius)+(2*factor*bound*radius+radius*radius) :=
      add_le_add firstBound secondBound
    _ = _ := by ring

theorem cross_positive_of_bounded_perturbation {factor bound radius : Int}
    (boundNonnegative : 0 ≤ bound) (radiusNonnegative : 0 ≤ radius)
    (spacing : 4*bound*radius+2*radius*radius+1 < factor)
    {first second firstOut secondOut : Cell}
    (firstBounds : |first.1| ≤ bound ∧ |first.2| ≤ bound)
    (secondBounds : |second.1| ≤ bound ∧ |second.2| ≤ bound)
    (firstPerturbed : BoundedVectorPerturbation radius factor first firstOut)
    (secondPerturbed : BoundedVectorPerturbation radius factor second secondOut)
    (ordered : 0 < cross first second) : 0 < cross firstOut secondOut := by
  have sumNonnegative : 0 ≤ 4*bound*radius+2*radius*radius := by positivity
  have factorPositive : 0 < factor := by omega
  have factorAtLeastOne : 1 ≤ factor := by omega
  have error := bounded_cross_perturbation factorPositive.le boundNonnegative radiusNonnegative
    firstBounds secondBounds firstPerturbed secondPerturbed
  have scaledSpacing := mul_lt_mul_of_pos_left spacing factorPositive
  have constantBound := mul_le_mul_of_nonneg_right factorAtLeastOne (by positivity : 0 ≤ 2*radius*radius)
  have crossAtLeastOne : 1 ≤ cross first second := by omega
  have scaledCross := mul_le_mul_of_nonneg_left crossAtLeastOne (by positivity : 0 ≤ factor*factor)
  have errorLower := (abs_le.mp error).1
  nlinarith

end LeanTrominoes.GridSegment
