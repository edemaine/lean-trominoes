/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.RationalAffineClipInterval

/-! # The open interval between two boundary contacts lies strictly inside the rectangle -/
namespace LeanTrominoes.RationalAffineBoundary

theorem open_clip_strict_inside {width height base slope : ℚ} (widthPositive : 0 < width) (heightPositive : 0 < height)
    (baseNotBottom : base ≠ 0) (baseNotTop : base ≠ height) {first last point : ℚ × ℚ}
    (firstContact : Contact width height base slope first) (lastContact : Contact width height base slope last)
    (before : first.1 < point.1) (after : point.1 < last.1) (onLine : point.2 = base+slope*point.1) :
    (0 < point.1 ∧ point.1 < width) ∧ (0 < point.2 ∧ point.2 < height) := by
  have firstPoint := firstContact.closedPoint widthPositive heightPositive
  have lastPoint := lastContact.closedPoint widthPositive heightPositive
  have closed := (closed_clip_x_interval widthPositive heightPositive baseNotBottom baseNotTop firstContact lastContact
    (before.trans after) onLine).mpr ⟨before.le,after.le⟩
  refine ⟨⟨by linarith [firstPoint.2.1.1],by linarith [lastPoint.2.1.2]⟩,?_⟩
  rcases lt_trichotomy slope 0 with negative | zero | positive
  · have firstGap := mul_neg_of_neg_of_pos negative (sub_pos.mpr before)
    have lastGap := mul_neg_of_neg_of_pos negative (sub_pos.mpr after)
    constructor <;> nlinarith [firstContact.1,onLine,lastContact.1,firstPoint.2.2.2,lastPoint.2.2.1]
  · have yBase : point.2 = base := by simpa [zero] using onLine
    have bounds := closed.2.2
    rw [yBase] at bounds ⊢
    exact ⟨lt_of_le_of_ne bounds.1 (Ne.symm baseNotBottom),lt_of_le_of_ne bounds.2 baseNotTop⟩
  · have firstGap := mul_pos positive (sub_pos.mpr before)
    have lastGap := mul_pos positive (sub_pos.mpr after)
    constructor <;> nlinarith [firstContact.1,onLine,lastContact.1,firstPoint.2.2.1,lastPoint.2.2.2]

end LeanTrominoes.RationalAffineBoundary
