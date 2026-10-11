/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentOrderedLeftRayTubes

/-! # Bounded core estimates under reversal and horizontal reflection -/
namespace LeanTrominoes.GridSegment

theorem RealTubeContains.reverse {segment : GridSegment} {radius : ℝ} {point : ℝ × ℝ}
    (contains : segment.RealTubeContains radius point) : segment.reverse.RealTubeContains radius point := by
  obtain ⟨original,originalContains,x,y⟩ := contains
  exact ⟨original,(realContains_reverse segment original).mpr originalContains,x,y⟩

theorem BoundedEndpointPerturbation.reverse {radius factor : Int} {original output : GridSegment}
    (perturbed : BoundedEndpointPerturbation radius factor original output) :
    BoundedEndpointPerturbation radius factor original.reverse output.reverse :=
  ⟨perturbed.2,perturbed.1⟩

theorem BoundedEndpointPerturbation.mirrorX {radius factor : Int} {original output : GridSegment}
    (perturbed : BoundedEndpointPerturbation radius factor original output) :
    BoundedEndpointPerturbation radius factor original.mirrorX output.mirrorX := by
  change (|-output.start.1-factor*(-original.start.1)| ≤ radius ∧
    |output.start.2-factor*original.start.2| ≤ radius) ∧
    (|-output.finish.1-factor*(-original.finish.1)| ≤ radius ∧
    |output.finish.2-factor*original.finish.2| ≤ radius)
  rw [show -output.start.1-factor*(-original.start.1) = -(output.start.1-factor*original.start.1) by ring,
    show -output.finish.1-factor*(-original.finish.1) = -(output.finish.1-factor*original.finish.1) by ring,
    abs_neg,abs_neg]
  exact perturbed

theorem perturbed_left_core_slope {radius factor bound : Int} {original core : GridSegment}
    (perturbed : BoundedEndpointPerturbation radius factor original core)
    (radiusNonnegative : 0 ≤ radius) (boundNonnegative : 0 ≤ bound) (spacing : 4*radius < factor)
    (leftward : original.direction.1 < 0) (verticalBound : |original.direction.2| ≤ bound) :
    core.direction.1 < 0 ∧ |core.realSlope| ≤ (2*bound+1 : Int) := by
  have bounds := perturbed_right_core_slope perturbed.mirrorX radiusNonnegative boundNonnegative spacing
    (by simp only [direction_mirrorX]; omega) (by simpa only [direction_mirrorX] using verticalBound)
  refine ⟨?_,?_⟩
  · simpa only [direction_mirrorX,neg_pos] using bounds.1
  · simpa only [realSlope_mirrorX,abs_neg] using bounds.2

theorem cross_negative_of_bounded_perturbation {factor bound radius : Int}
    (boundNonnegative : 0 ≤ bound) (radiusNonnegative : 0 ≤ radius)
    (spacing : 4*bound*radius+2*radius*radius+1 < factor)
    {first second firstOut secondOut : Cell}
    (firstBounds : |first.1| ≤ bound ∧ |first.2| ≤ bound)
    (secondBounds : |second.1| ≤ bound ∧ |second.2| ≤ bound)
    (firstPerturbed : BoundedVectorPerturbation radius factor first firstOut)
    (secondPerturbed : BoundedVectorPerturbation radius factor second secondOut)
    (ordered : cross first second < 0) : cross firstOut secondOut < 0 := by
  have swapped : 0 < cross second first := by simp only [cross] at ordered ⊢; nlinarith
  have preserved := cross_positive_of_bounded_perturbation boundNonnegative radiusNonnegative spacing
    secondBounds firstBounds secondPerturbed firstPerturbed swapped
  simp only [cross] at preserved ⊢
  nlinarith

end LeanTrominoes.GridSegment
