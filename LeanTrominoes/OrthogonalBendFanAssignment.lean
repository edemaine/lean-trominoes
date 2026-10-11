/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.OrthogonalBendFanTemplates
import LeanTrominoes.GridSegmentStraightRayKeys

/-! # Assigning sign-preserving bend fans to rational ray keys

The upper ray is selected by its outward height, reversing the slope sign
on the left side. Distinct ray keys always select a certified valid fan,
even when both rays have the same sign class.
-/
namespace LeanTrominoes.OrthogonalDrawingRefinement.BendFan

def rayClass : StraightRayKey → RayClass
  | .right slope => if 0 < slope then .eastUp else if slope < 0 then .eastDown else .east
  | .left slope => if slope < 0 then .westUp else if 0 < slope then .westDown else .west
  | .up => .north
  | .down => .south

def outwardHeight : StraightRayKey → ℚ
  | .right slope => slope
  | .left slope => -slope
  | .up => 1
  | .down => -1

def horizontalSign : StraightRayKey → Int
  | .right _ => 1
  | .left _ => -1
  | .up | .down => 0

def verticalSign (key : StraightRayKey) : Int :=
  if 0 < outwardHeight key then 1 else if outwardHeight key < 0 then -1 else 0

def assignedProfile (first second : StraightRayKey) : Profile :=
  if outwardHeight first < outwardHeight second then ⟨rayClass second,rayClass first⟩
  else ⟨rayClass first,rayClass second⟩

def assignedIndex (first second : StraightRayKey) : Bool :=
  decide (outwardHeight first < outwardHeight second)

theorem assignedProfile_valid {first second : StraightRayKey} (different : first ≠ second) :
    (assignedProfile first second).Valid := by
  unfold assignedProfile
  split_ifs with ordered
  all_goals
    cases first <;> cases second <;>
      simp only [rayClass,outwardHeight] at * <;>
      (try split_ifs at *) <;>
      simp_all [Profile.Valid,Profile.sameSide,RayClass.horizontalSign,RayClass.verticalSign] <;>
      first | linarith | exact different (by linarith)

theorem rayClass_horizontalSign (key : StraightRayKey) :
    (rayClass key).horizontalSign = horizontalSign key := by
  cases key <;> simp only [rayClass,horizontalSign] <;> (try split_ifs) <;> rfl

theorem rayClass_verticalSign (key : StraightRayKey) :
    (rayClass key).verticalSign = verticalSign key := by
  cases key <;> simp only [rayClass,verticalSign,outwardHeight]
  all_goals split_ifs <;> simp_all [RayClass.verticalSign] <;> linarith

theorem assignedProfile_first_class (first second : StraightRayKey) :
    (if assignedIndex first second then (assignedProfile first second).second
      else (assignedProfile first second).first) = rayClass first := by
  by_cases ordered : outwardHeight first < outwardHeight second <;>
    simp [assignedIndex,assignedProfile,ordered]

theorem assignedProfile_second_class (first second : StraightRayKey) :
    (if !(assignedIndex first second) then (assignedProfile first second).second
      else (assignedProfile first second).first) = rayClass second := by
  by_cases ordered : outwardHeight first < outwardHeight second <;>
    simp [assignedIndex,assignedProfile,ordered]

theorem assignedProfile_sameSide {first second : StraightRayKey}
    (same : horizontalSign first = horizontalSign second) (nonzero : horizontalSign first ≠ 0) :
    (assignedProfile first second).sameSide := by
  unfold assignedProfile
  split_ifs <;> simp only [Profile.sameSide,rayClass_horizontalSign] <;> simp_all

theorem assignedProfile_port_gap {first second : StraightRayKey} (different : first ≠ second)
    (same : horizontalSign first = horizontalSign second) (nonzero : horizontalSign first ≠ 0)
    (ordered : outwardHeight first < outwardHeight second) :
    ((assignedProfile first second).port (assignedIndex first second)).2+2 ≤
      ((assignedProfile first second).port (!(assignedIndex first second))).2 := by
  have gap := sameSide_port_gap (assignedProfile first second) (assignedProfile_valid different)
    (assignedProfile_sameSide same nonzero)
  simpa [assignedIndex,ordered] using gap

end LeanTrominoes.OrthogonalDrawingRefinement.BendFan
