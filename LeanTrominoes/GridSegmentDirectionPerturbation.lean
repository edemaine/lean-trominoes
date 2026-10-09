/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentRayContacts

/-! # Quantitative stability of directions at perturbed segment endpoints -/
namespace LeanTrominoes.GridSegment

def VectorPerturbation (factor : Int) (original output : Cell) : Prop :=
  |output.1-factor*original.1|≤2 ∧ |output.2-factor*original.2|≤2

theorem EndpointPerturbation.direction {factor : Int} {original output : GridSegment}
    (perturbed : EndpointPerturbation factor original output) :
    VectorPerturbation factor original.direction output.direction := by
  have coordinate (first last firstOut lastOut : Int)
      (firstBound : |firstOut-factor*first|≤1) (lastBound : |lastOut-factor*last|≤1) :
      |(lastOut-firstOut)-factor*(last-first)|≤2 := calc
    _ = |(lastOut-factor*last)-(firstOut-factor*first)| := by congr 1; ring
    _ ≤ |lastOut-factor*last| + |firstOut-factor*first| := abs_sub _ _
    _ ≤ 1+1 := add_le_add lastBound firstBound
    _ = _ := rfl
  exact ⟨coordinate _ _ _ _ perturbed.1.1 perturbed.2.1,
    coordinate _ _ _ _ perturbed.1.2 perturbed.2.2⟩

theorem product_perturbation_bound {factor bound a b outputA outputB : Int}
    (factorNonnegative : 0≤factor) (boundNonnegative : 0≤bound)
    (aBound : |a|≤bound) (bBound : |b|≤bound)
    (aPerturbed : |outputA-factor*a|≤2) (bPerturbed : |outputB-factor*b|≤2) :
    |outputA*outputB-factor*factor*(a*b)|≤4*factor*bound+4 := by
  let ea := outputA-factor*a
  let eb := outputB-factor*b
  have eaBound : |ea|≤2 := aPerturbed
  have ebBound : |eb|≤2 := bPerturbed
  have firstBound : |a*eb|≤2*bound := by
    rw [abs_mul]
    nlinarith [mul_le_mul aBound ebBound (abs_nonneg _) boundNonnegative]
  have secondBound : |ea*b|≤2*bound := by
    rw [abs_mul]
    nlinarith [mul_le_mul eaBound bBound (abs_nonneg _) (by norm_num : (0:Int)≤2)]
  have errorBound : |ea*eb|≤4 := by
    rw [abs_mul]
    exact mul_le_mul eaBound ebBound (abs_nonneg _) (by norm_num)
  calc
    _ = |factor*(a*eb+ea*b)+ea*eb| := by congr 1; dsimp [ea,eb]; ring
    _ ≤ |factor*(a*eb+ea*b)| + |ea*eb| := abs_add_le _ _
    _ = factor*|a*eb+ea*b| + |ea*eb| := by rw [abs_mul,abs_of_nonneg factorNonnegative]
    _ ≤ factor*(|a*eb| + |ea*b|)+4 := add_le_add
      (mul_le_mul_of_nonneg_left (abs_add_le _ _) factorNonnegative) errorBound
    _ ≤ factor*(2*bound+2*bound)+4 := add_le_add
      (mul_le_mul_of_nonneg_left (add_le_add firstBound secondBound) factorNonnegative) (le_refl 4)
    _ = _ := by ring

theorem cross_perturbation_bound {factor bound : Int} (factorNonnegative : 0≤factor) (boundNonnegative : 0≤bound)
    {first second firstOut secondOut : Cell}
    (firstBounds : |first.1|≤bound ∧ |first.2|≤bound) (secondBounds : |second.1|≤bound ∧ |second.2|≤bound)
    (firstPerturbed : VectorPerturbation factor first firstOut) (secondPerturbed : VectorPerturbation factor second secondOut) :
    |cross firstOut secondOut-factor*factor*cross first second|≤8*factor*bound+8 := by
  have firstBound := product_perturbation_bound factorNonnegative boundNonnegative
    firstBounds.1 secondBounds.2 firstPerturbed.1 secondPerturbed.2
  have secondBound := product_perturbation_bound factorNonnegative boundNonnegative
    firstBounds.2 secondBounds.1 firstPerturbed.2 secondPerturbed.1
  calc
    _ = |(firstOut.1*secondOut.2-factor*factor*(first.1*second.2))-
        (firstOut.2*secondOut.1-factor*factor*(first.2*second.1))| := by congr 1; unfold cross; ring
    _ ≤ |firstOut.1*secondOut.2-factor*factor*(first.1*second.2)| +
        |firstOut.2*secondOut.1-factor*factor*(first.2*second.1)| := abs_sub _ _
    _ ≤ (4*factor*bound+4)+(4*factor*bound+4) := add_le_add firstBound secondBound
    _ = _ := by ring

theorem dot_perturbation_bound {factor bound : Int} (factorNonnegative : 0≤factor) (boundNonnegative : 0≤bound)
    {first second firstOut secondOut : Cell}
    (firstBounds : |first.1|≤bound ∧ |first.2|≤bound) (secondBounds : |second.1|≤bound ∧ |second.2|≤bound)
    (firstPerturbed : VectorPerturbation factor first firstOut) (secondPerturbed : VectorPerturbation factor second secondOut) :
    |dot firstOut secondOut-factor*factor*dot first second|≤8*factor*bound+8 := by
  have firstBound := product_perturbation_bound factorNonnegative boundNonnegative
    firstBounds.1 secondBounds.1 firstPerturbed.1 secondPerturbed.1
  have secondBound := product_perturbation_bound factorNonnegative boundNonnegative
    firstBounds.2 secondBounds.2 firstPerturbed.2 secondPerturbed.2
  calc
    _ = |(firstOut.1*secondOut.1-factor*factor*(first.1*second.1))+
        (firstOut.2*secondOut.2-factor*factor*(first.2*second.2))| := by congr 1; unfold dot; ring
    _ ≤ |firstOut.1*secondOut.1-factor*factor*(first.1*second.1)| +
        |firstOut.2*secondOut.2-factor*factor*(first.2*second.2)| := abs_add_le _ _
    _ ≤ (4*factor*bound+4)+(4*factor*bound+4) := add_le_add firstBound secondBound
    _ = _ := by ring

private theorem error_smaller_than_square {factor bound : Int} (boundNonnegative : 0≤bound) (spacing : 8*bound+8<factor) :
    8*factor*bound+8<factor*factor := by
  have positive : 0<factor := by omega
  have scaled := mul_lt_mul_of_pos_right spacing positive
  nlinarith

theorem ray_criterion_perturb {factor bound : Int} (boundNonnegative : 0≤bound) (spacing : 8*bound+8<factor)
    {first second firstOut secondOut : Cell}
    (firstBounds : |first.1|≤bound ∧ |first.2|≤bound) (secondBounds : |second.1|≤bound ∧ |second.2|≤bound)
    (firstPerturbed : VectorPerturbation factor first firstOut) (secondPerturbed : VectorPerturbation factor second secondOut)
    (rays : cross first second≠0 ∨ dot first second<0) :
    cross firstOut secondOut≠0 ∨ dot firstOut secondOut<0 := by
  have factorPositive : 0<factor := by omega
  have errorSmall := error_smaller_than_square boundNonnegative spacing
  rcases rays with crossed | opposite
  · left
    intro zero
    have error := cross_perturbation_bound factorPositive.le boundNonnegative firstBounds secondBounds firstPerturbed secondPerturbed
    rw [zero,zero_sub,abs_neg,abs_mul,abs_mul,abs_of_pos factorPositive] at error
    have integerGap : 1≤|cross first second| := by have := abs_pos.mpr crossed; omega
    nlinarith
  · right
    have error := (abs_le.mp (dot_perturbation_bound factorPositive.le boundNonnegative
      firstBounds secondBounds firstPerturbed secondPerturbed)).2
    have integerGap : dot first second≤-1 := by omega
    have scaled := mul_le_mul_of_nonneg_left integerGap (mul_nonneg factorPositive.le factorPositive.le)
    nlinarith

theorem shared_start_perturbations_contact {factor bound : Int} (boundNonnegative : 0≤bound) (spacing : 8*bound+8<factor)
    {first second firstOutput secondOutput : GridSegment}
    (firstBounds : |first.direction.1|≤bound ∧ |first.direction.2|≤bound)
    (secondBounds : |second.direction.1|≤bound ∧ |second.direction.2|≤bound)
    (rays : cross first.direction second.direction≠0 ∨ dot first.direction second.direction<0)
    (firstPerturbed : EndpointPerturbation factor first firstOutput)
    (secondPerturbed : EndpointPerturbation factor second secondOutput)
    (sameStart : firstOutput.start=secondOutput.start) {p : ℝ × ℝ}
    (firstMember : firstOutput.RealContains p) (secondMember : secondOutput.RealContains p) :
    p=((firstOutput.start.1:ℝ),(firstOutput.start.2:ℝ)) :=
  shared_start_contact sameStart
    (ray_criterion_perturb boundNonnegative spacing firstBounds secondBounds firstPerturbed.direction secondPerturbed.direction rays)
    firstMember secondMember

end LeanTrominoes.GridSegment
