/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.RationalAffineContactOrder

/-! # The part of an affine line in a rectangle is exactly its contact interval -/
namespace LeanTrominoes.RationalAffineBoundary

def ClosedPoint (width height base slope : ℚ) (point : ℚ × ℚ) : Prop :=
  point.2 = base+slope*point.1 ∧ (0 ≤ point.1 ∧ point.1 ≤ width) ∧ (0 ≤ point.2 ∧ point.2 ≤ height)

theorem Contact.closedPoint {width height base slope : ℚ} (widthPositive : 0 < width) (heightPositive : 0 < height)
    {point : ℚ × ℚ} (contact : Contact width height base slope point) : ClosedPoint width height base slope point :=
  ⟨contact.1,contact_coordinate_bounds widthPositive heightPositive contact⟩

theorem closed_points_no_middle_boundary {width height base slope : ℚ} (widthPositive : 0 < width) (heightPositive : 0 < height)
    (baseNotBottom : base ≠ 0) (baseNotTop : base ≠ height) {first middle last : ℚ × ℚ}
    (firstPoint : ClosedPoint width height base slope first) (middleContact : Contact width height base slope middle)
    (lastPoint : ClosedPoint width height base slope last) (before : first.1 < middle.1) (after : middle.1 < last.1) : False := by
  have xPositive : 0 < middle.1 := by linarith [firstPoint.2.1.1]
  have xBound : middle.1 < width := by linarith [lastPoint.2.1.2]
  have middleOnSide : middle.2 = 0 ∨ middle.2 = height := by
    rcases middleContact.2 with ⟨side,_,_⟩ | ⟨side,_,_⟩
    · rcases side with side | side <;> linarith
    · exact side
  have yInside : 0 < middle.2 ∧ middle.2 < height := by
    rcases lt_trichotomy slope 0 with negative | zero | positive
    · have firstGap := mul_neg_of_neg_of_pos negative (sub_pos.mpr before)
      have lastGap := mul_neg_of_neg_of_pos negative (sub_pos.mpr after)
      constructor <;> nlinarith [firstPoint.1,middleContact.1,lastPoint.1,firstPoint.2.2.2,lastPoint.2.2.1]
    · have yBase : middle.2 = base := by simpa [zero] using middleContact.1
      have bounds := contact_coordinate_bounds widthPositive heightPositive middleContact
      rw [yBase] at bounds ⊢
      exact ⟨lt_of_le_of_ne bounds.2.1 baseNotBottom.symm,lt_of_le_of_ne bounds.2.2 baseNotTop⟩
    · have firstGap := mul_pos positive (sub_pos.mpr before)
      have lastGap := mul_pos positive (sub_pos.mpr after)
      constructor <;> nlinarith [firstPoint.1,middleContact.1,lastPoint.1,firstPoint.2.2.1,lastPoint.2.2.2]
  rcases middleOnSide with bottom | top <;> linarith

theorem closed_clip_x_interval {width height base slope : ℚ} (widthPositive : 0 < width) (heightPositive : 0 < height)
    (baseNotBottom : base ≠ 0) (baseNotTop : base ≠ height) {first last point : ℚ × ℚ}
    (firstContact : Contact width height base slope first) (lastContact : Contact width height base slope last)
    (ordered : first.1 < last.1) (onLine : point.2 = base+slope*point.1) :
    ClosedPoint width height base slope point ↔ first.1 ≤ point.1 ∧ point.1 ≤ last.1 := by
  have firstPoint := firstContact.closedPoint widthPositive heightPositive
  have lastPoint := lastContact.closedPoint widthPositive heightPositive
  constructor
  · intro inside
    constructor
    · by_contra notAfter
      exact closed_points_no_middle_boundary widthPositive heightPositive baseNotBottom baseNotTop inside firstContact lastPoint
        (lt_of_not_ge notAfter) ordered
    · by_contra notBefore
      exact closed_points_no_middle_boundary widthPositive heightPositive baseNotBottom baseNotTop firstPoint lastContact inside
        ordered (lt_of_not_ge notBefore)
  · intro interval
    refine ⟨onLine,⟨by linarith [firstPoint.2.1.1],by linarith [lastPoint.2.1.2]⟩,?_⟩
    by_cases nonnegative : 0 ≤ slope
    · have firstGap := mul_nonneg nonnegative (sub_nonneg.mpr interval.1)
      have lastGap := mul_nonneg nonnegative (sub_nonneg.mpr interval.2)
      constructor <;> nlinarith [firstContact.1,lastContact.1,firstPoint.2.2.1,lastPoint.2.2.2]
    · have firstGap := mul_nonpos_of_nonpos_of_nonneg (le_of_lt (lt_of_not_ge nonnegative)) (sub_nonneg.mpr interval.1)
      have lastGap := mul_nonpos_of_nonpos_of_nonneg (le_of_lt (lt_of_not_ge nonnegative)) (sub_nonneg.mpr interval.2)
      constructor <;> nlinarith [firstContact.1,lastContact.1,firstPoint.2.2.2,lastPoint.2.2.1]

end LeanTrominoes.RationalAffineBoundary
