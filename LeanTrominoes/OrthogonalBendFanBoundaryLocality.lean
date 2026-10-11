/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.OrthogonalBendFanRaySigns

/-! # Assigned bend fans remain inside scaled parent rectangles

At a rectangle boundary, both incident rays point into its coordinate
half-plane. The assigned fan preserves this half-plane. At every other
integer coordinate, scaling leaves room for the complete fan.
-/
namespace LeanTrominoes.OrthogonalDrawingRefinement.BendFan

theorem assignedProfile_preserves_halfPlanes {first second : StraightRayKey} (different : first ≠ second)
    (index : Bool) {point : Cell} (member : point ∈ (assignedProfile first second).route index) :
    ((0 ≤ horizontalSign first ∧ 0 ≤ horizontalSign second) → 0 ≤ point.1) ∧
      ((horizontalSign first ≤ 0 ∧ horizontalSign second ≤ 0) → point.1 ≤ 0) ∧
      ((0 ≤ verticalSign first ∧ 0 ≤ verticalSign second) → 0 ≤ point.2) ∧
      ((verticalSign first ≤ 0 ∧ verticalSign second ≤ 0) → point.2 ≤ 0) := by
  have bounds := preserves_halfPlanes (assignedProfile first second) index (assignedProfile_valid different) point member
  by_cases ordered : outwardHeight first < outwardHeight second
  · simpa only [assignedProfile,if_pos ordered,rayClass_horizontalSign,rayClass_verticalSign,and_comm] using bounds
  · simpa only [assignedProfile,if_neg ordered,rayClass_horizontalSign,rayClass_verticalSign] using bounds

theorem scaled_coordinate_inside {lower upper center displacement factor : Int}
    (spacing : 10 ≤ factor) (inside : lower ≤ center ∧ center ≤ upper) (small : |displacement| ≤ 10)
    (lowerSide : center = lower → 0 ≤ displacement) (upperSide : center = upper → displacement ≤ 0) :
    factor*lower ≤ factor*center+displacement ∧ factor*center+displacement ≤ factor*upper := by
  have smallBounds := abs_le.mp small
  constructor
  · by_cases boundary : center = lower
    · rw [boundary]
      exact le_add_of_nonneg_right (lowerSide boundary)
    · have margin : factor ≤ factor*(center-lower) := by
        have scaled := mul_le_mul_of_nonneg_left (show 1 ≤ center-lower by omega) (by omega : 0 ≤ factor)
        simpa only [mul_one] using scaled
      nlinarith
  · by_cases boundary : center = upper
    · rw [boundary]
      exact add_le_of_nonpos_right (upperSide boundary)
    · have margin : factor ≤ factor*(upper-center) := by
        have scaled := mul_le_mul_of_nonneg_left (show 1 ≤ upper-center by omega) (by omega : 0 ≤ factor)
        simpa only [mul_one] using scaled
      nlinarith

theorem assignedProfile_scaled_inside_rectangle {first second : StraightRayKey} (different : first ≠ second)
    (index : Bool) {point center : Cell} {left right bottom top factor : Int} (spacing : 10 ≤ factor)
    (inside : left ≤ center.1 ∧ center.1 ≤ right ∧ bottom ≤ center.2 ∧ center.2 ≤ top)
    (leftSide : center.1 = left → 0 ≤ horizontalSign first ∧ 0 ≤ horizontalSign second)
    (rightSide : center.1 = right → horizontalSign first ≤ 0 ∧ horizontalSign second ≤ 0)
    (bottomSide : center.2 = bottom → 0 ≤ verticalSign first ∧ 0 ≤ verticalSign second)
    (topSide : center.2 = top → verticalSign first ≤ 0 ∧ verticalSign second ≤ 0)
    (member : point ∈ (assignedProfile first second).route index) :
    factor*left ≤ factor*center.1+point.1 ∧ factor*center.1+point.1 ≤ factor*right ∧
      factor*bottom ≤ factor*center.2+point.2 ∧ factor*center.2+point.2 ≤ factor*top := by
  have bounds := route_bounds (assignedProfile first second) index point member
  have halfPlanes := assignedProfile_preserves_halfPlanes different index member
  have horizontal := scaled_coordinate_inside spacing ⟨inside.1,inside.2.1⟩
    (abs_le.mpr ⟨by omega,by omega⟩ : |point.1| ≤ 10)
    (fun boundary => halfPlanes.1 (leftSide boundary)) (fun boundary => halfPlanes.2.1 (rightSide boundary))
  have vertical := scaled_coordinate_inside spacing ⟨inside.2.2.1,inside.2.2.2⟩
    (abs_le.mpr ⟨bounds.2.2.1,bounds.2.2.2⟩)
    (fun boundary => halfPlanes.2.2.1 (bottomSide boundary)) (fun boundary => halfPlanes.2.2.2 (topSide boundary))
  exact ⟨horizontal.1,horizontal.2,vertical.1,vertical.2⟩

end LeanTrominoes.OrthogonalDrawingRefinement.BendFan
