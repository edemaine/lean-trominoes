/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentRealIntersection

/-! # Finite certificates for closed segment contacts at one prescribed point -/
namespace LeanTrominoes.GridSegment

def BoxIntersectionIsPoint (first second : GridSegment) (center : Cell) : Prop :=
  (max (min first.start.1 first.finish.1) (min second.start.1 second.finish.1) ≤
      min (max first.start.1 first.finish.1) (max second.start.1 second.finish.1) ∧
    max (min first.start.2 first.finish.2) (min second.start.2 second.finish.2) ≤
      min (max first.start.2 first.finish.2) (max second.start.2 second.finish.2)) →
  max (min first.start.1 first.finish.1) (min second.start.1 second.finish.1) = center.1 ∧
    min (max first.start.1 first.finish.1) (max second.start.1 second.finish.1) = center.1 ∧
    max (min first.start.2 first.finish.2) (min second.start.2 second.finish.2) = center.2 ∧
    min (max first.start.2 first.finish.2) (max second.start.2 second.finish.2) = center.2

instance (first second : GridSegment) (center : Cell) :
    Decidable (BoxIntersectionIsPoint first second center) := by
  unfold BoxIntersectionIsPoint
  infer_instance

theorem real_intersection_eq_of_box_certificate {first second : GridSegment} {center : Cell}
    (certificate : BoxIntersectionIsPoint first second center) {point : ℝ × ℝ}
    (firstMember : first.RealContains point) (secondMember : second.RealContains point) :
    point = ((center.1 : ℝ),(center.2 : ℝ)) := by
  have firstBox := realBoxContains_of_realContains firstMember
  have secondBox := realBoxContains_of_realContains secondMember
  have xlo : (max (min first.start.1 first.finish.1) (min second.start.1 second.finish.1) : Int) ≤ point.1 := by
    rw [Int.cast_max]
    exact max_le firstBox.1 secondBox.1
  have xhi : point.1 ≤ (min (max first.start.1 first.finish.1) (max second.start.1 second.finish.1) : Int) := by
    rw [Int.cast_min]
    exact le_min firstBox.2.1 secondBox.2.1
  have ylo : (max (min first.start.2 first.finish.2) (min second.start.2 second.finish.2) : Int) ≤ point.2 := by
    rw [Int.cast_max]
    exact max_le firstBox.2.2.1 secondBox.2.2.1
  have yhi : point.2 ≤ (min (max first.start.2 first.finish.2) (max second.start.2 second.finish.2) : Int) := by
    rw [Int.cast_min]
    exact le_min firstBox.2.2.2 secondBox.2.2.2
  have occupied :
      max (min first.start.1 first.finish.1) (min second.start.1 second.finish.1) ≤
        min (max first.start.1 first.finish.1) (max second.start.1 second.finish.1) ∧
      max (min first.start.2 first.finish.2) (min second.start.2 second.finish.2) ≤
        min (max first.start.2 first.finish.2) (max second.start.2 second.finish.2) :=
    ⟨by exact_mod_cast (le_trans xlo xhi),by exact_mod_cast (le_trans ylo yhi)⟩
  obtain ⟨xl,xh,yl,yh⟩ := certificate occupied
  rw [xl] at xlo
  rw [xh] at xhi
  rw [yl] at ylo
  rw [yh] at yhi
  exact Prod.ext (le_antisymm xhi xlo) (le_antisymm yhi ylo)

end LeanTrominoes.GridSegment
