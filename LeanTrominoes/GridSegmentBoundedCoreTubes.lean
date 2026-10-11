/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentDigitalRoute
import LeanTrominoes.GridSegmentBoundedDirectionPerturbation

/-! # Rasterized cores with bounded endpoint displacement

The first refinement leaves room for constant-size vertex connectors. The
second refinement rasterizes the straight cores between their anchors.
Nonincident cores remain disjoint with a first factor linear in the original
direction bound, regardless of the second factor.
-/
namespace LeanTrominoes.GridSegment

def BoundedEndpointPerturbation (radius factor : Int) (original output : GridSegment) : Prop :=
  (|output.start.1-factor*original.start.1| ≤ radius ∧
    |output.start.2-factor*original.start.2| ≤ radius) ∧
  (|output.finish.1-factor*original.finish.1| ≤ radius ∧
    |output.finish.2-factor*original.finish.2| ≤ radius)

theorem BoundedEndpointPerturbation.direction {radius factor : Int} {original output : GridSegment}
    (perturbed : BoundedEndpointPerturbation radius factor original output) :
    BoundedVectorPerturbation (2*radius) factor original.direction output.direction := by
  have coordinate (first last firstOut lastOut : Int)
      (firstBound : |firstOut-factor*first| ≤ radius) (lastBound : |lastOut-factor*last| ≤ radius) :
      |(lastOut-firstOut)-factor*(last-first)| ≤ 2*radius := by
    calc
      _ = |(lastOut-factor*last)-(firstOut-factor*first)| := by congr 1; ring
      _ ≤ _ := abs_sub _ _
      _ ≤ radius+radius := add_le_add lastBound firstBound
      _ = _ := by ring
  exact ⟨coordinate _ _ _ _ perturbed.1.1 perturbed.2.1,
    coordinate _ _ _ _ perturbed.1.2 perturbed.2.2⟩

theorem segment_scale_scale (segment : GridSegment) (first second : Int) :
    (segment.scale first).scale second = segment.scale (second*first) := by
  cases segment
  simp only [scale,Cell.scale_scale]

theorem BoundedEndpointPerturbation.tube {radius factor : Int} {original output : GridSegment}
    (perturbed : BoundedEndpointPerturbation radius factor original output)
    {point : ℝ × ℝ} (contains : output.RealContains point) :
    (original.scale factor).RealTubeContains radius point := by
  have start : (original.scale factor).RealTubeContains radius (realCell output.start) := by
    refine ⟨realCell (Cell.scale factor original.start),realContains_start _,?_,?_⟩
    · dsimp [realCell,Cell.scale]
      exact_mod_cast perturbed.1.1
    · dsimp [realCell,Cell.scale]
      exact_mod_cast perturbed.1.2
  have finish : (original.scale factor).RealTubeContains radius (realCell output.finish) := by
    refine ⟨realCell (Cell.scale factor original.finish),realContains_finish _,?_,?_⟩
    · dsimp [realCell,Cell.scale]
      exact_mod_cast perturbed.2.1
    · dsimp [realCell,Cell.scale]
      exact_mod_cast perturbed.2.2
  exact start.segment finish contains

theorem BoundedEndpointPerturbation.scaled_tube {radius firstFactor secondFactor : Int}
    {original output : GridSegment}
    (perturbed : BoundedEndpointPerturbation radius firstFactor original output)
    (positive : 0 < secondFactor) {point : ℝ × ℝ} (contains : (output.scale secondFactor).RealContains point) :
    (original.scale (secondFactor*firstFactor)).RealTubeContains ((secondFactor : ℝ)*radius) point := by
  have realNonzero : (secondFactor : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt positive
  have originalContains := (realContains_scale_inverse output (ne_of_gt positive) point).mp contains
  have scaled := (perturbed.tube originalContains).scale (factor := secondFactor) positive.le
  simpa only [segment_scale_scale,mul_div_cancel₀ _ realNonzero,Prod.mk.eta] using scaled

theorem BoundedEndpointPerturbation.digitalRoute_tube {radius firstFactor secondFactor : Int}
    {original output : GridSegment}
    (perturbed : BoundedEndpointPerturbation radius firstFactor original output)
    (positive : 0 < secondFactor) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (output.scale secondFactor).digitalRoute point) :
    (original.scale (secondFactor*firstFactor)).RealTubeContains ((secondFactor : ℝ)*radius+2) point :=
  ((output.scale secondFactor).digitalRoute_tube contains).compose
    (fun _ contains => perturbed.scaled_tube positive contains)

theorem bounded_core_digitalRoutes_disjoint {bound radius firstFactor secondFactor : Int}
    (boundPositive : 1 ≤ bound) (radiusNonnegative : 0 ≤ radius) (secondPositive : 0 < secondFactor)
    (spacing : 4*bound*(radius+2) < firstFactor) {first second firstCore secondCore : GridSegment}
    (firstBounds : |first.direction.1| ≤ bound ∧ |first.direction.2| ≤ bound)
    (secondBounds : |second.direction.1| ≤ bound ∧ |second.direction.2| ≤ bound)
    (firstPerturbed : BoundedEndpointPerturbation radius firstFactor first firstCore)
    (secondPerturbed : BoundedEndpointPerturbation radius firstFactor second secondCore)
    (disjoint : ∀ point : ℝ × ℝ, first.RealContains point → ¬second.RealContains point)
    {point : ℝ × ℝ} (firstContains : GridPolyline.RealContains (firstCore.scale secondFactor).digitalRoute point) :
    ¬GridPolyline.RealContains (secondCore.scale secondFactor).digitalRoute point := by
  intro secondContains
  have firstTube := firstPerturbed.digitalRoute_tube secondPositive firstContains
  have secondTube := secondPerturbed.digitalRoute_tube secondPositive secondContains
  have tubeRadiusNonnegative : (0 : ℝ) ≤ (secondFactor : ℝ)*radius+2 := by positivity
  have tubeSpacing : 4*(bound : ℝ)*((secondFactor : ℝ)*radius+2) < (secondFactor*firstFactor : Int) := by
    have secondAtLeastOne : (1 : ℝ) ≤ secondFactor := by exact_mod_cast (show 1 ≤ secondFactor by omega)
    have boundNonnegative : (0 : ℝ) ≤ bound := by exact_mod_cast (show 0 ≤ bound by omega)
    have realSpacing : 4*(bound : ℝ)*((radius : ℝ)+2) < firstFactor := by exact_mod_cast spacing
    have scaledSpacing := mul_lt_mul_of_pos_left realSpacing (by exact_mod_cast secondPositive : (0 : ℝ) < secondFactor)
    push_cast
    nlinarith [mul_nonneg boundNonnegative (sub_nonneg.mpr secondAtLeastOne)]
  exact scaled_tubes_disjoint boundPositive tubeRadiusNonnegative tubeSpacing firstBounds secondBounds disjoint point firstTube secondTube

end LeanTrominoes.GridSegment
