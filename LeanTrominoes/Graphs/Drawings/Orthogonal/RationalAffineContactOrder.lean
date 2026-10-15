/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.RationalAffineBoundaryContacts

/-! # Boundary contacts delimit one interval of an affine rectangle clip -/
namespace LeanTrominoes.RationalAffineBoundary

theorem contact_coordinate_bounds {width height base slope : ℚ} (widthPositive : 0 < width) (heightPositive : 0 < height)
    {point : ℚ × ℚ} (contact : Contact width height base slope point) :
    (0 ≤ point.1 ∧ point.1 ≤ width) ∧ (0 ≤ point.2 ∧ point.2 ≤ height) := by
  rcases contact.2 with ⟨side,lo,hi⟩ | ⟨side,lo,hi⟩
  all_goals rcases side with side | side <;> refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩ <;> linarith

theorem contact_eq_of_x_eq {width height base slope : ℚ} {first last : ℚ × ℚ}
    (firstContact : Contact width height base slope first) (lastContact : Contact width height base slope last)
    (sameX : first.1 = last.1) : first = last :=
  Prod.ext sameX (by rw [firstContact.1,lastContact.1,sameX])

theorem contacts_no_middle {width height base slope : ℚ} (widthPositive : 0 < width) (heightPositive : 0 < height)
    (baseNotBottom : base ≠ 0) (baseNotTop : base ≠ height) {first middle last : ℚ × ℚ}
    (firstContact : Contact width height base slope first) (middleContact : Contact width height base slope middle)
    (lastContact : Contact width height base slope last) (before : first.1 < middle.1) (after : middle.1 < last.1) : False := by
  have fb := contact_coordinate_bounds widthPositive heightPositive firstContact
  have lb := contact_coordinate_bounds widthPositive heightPositive lastContact
  have xPositive : 0 < middle.1 := by linarith [fb.1.1]
  have xBound : middle.1 < width := by linarith [lb.1.2]
  have middleOnSide : middle.2 = 0 ∨ middle.2 = height := by
    rcases middleContact.2 with ⟨side,_,_⟩ | ⟨side,_,_⟩
    · rcases side with side | side <;> linarith
    · exact side
  have yInside : 0 < middle.2 ∧ middle.2 < height := by
    rcases lt_trichotomy slope 0 with negative | zero | positive
    · have firstGap := mul_neg_of_neg_of_pos negative (sub_pos.mpr before)
      have lastGap := mul_neg_of_neg_of_pos negative (sub_pos.mpr after)
      constructor <;> nlinarith [firstContact.1,middleContact.1,lastContact.1,fb.2.2,lb.2.1]
    · have yBase : middle.2 = base := by simpa [zero] using middleContact.1
      have bounds := contact_coordinate_bounds widthPositive heightPositive middleContact
      rw [yBase] at bounds ⊢
      exact ⟨lt_of_le_of_ne bounds.2.1 baseNotBottom.symm,lt_of_le_of_ne bounds.2.2 baseNotTop⟩
    · have firstGap := mul_pos positive (sub_pos.mpr before)
      have lastGap := mul_pos positive (sub_pos.mpr after)
      constructor <;> nlinarith [firstContact.1,middleContact.1,lastContact.1,fb.2.1,lb.2.2]
  rcases middleOnSide with bottom | top <;> linarith

theorem contacts_are_two_endpoints {width height base slope : ℚ} (widthPositive : 0 < width) (heightPositive : 0 < height)
    (baseNotBottom : base ≠ 0) (baseNotTop : base ≠ height) {first last point : ℚ × ℚ}
    (firstContact : Contact width height base slope first) (lastContact : Contact width height base slope last)
    (ordered : first.1 < last.1) (contact : Contact width height base slope point) : point = first ∨ point = last := by
  rcases lt_trichotomy point.1 first.1 with before | same | after
  · exact (contacts_no_middle widthPositive heightPositive baseNotBottom baseNotTop contact firstContact lastContact before ordered).elim
  · exact Or.inl (contact_eq_of_x_eq contact firstContact same)
  · rcases lt_trichotomy point.1 last.1 with before | same | later
    · exact (contacts_no_middle widthPositive heightPositive baseNotBottom baseNotTop firstContact contact lastContact after before).elim
    · exact Or.inr (contact_eq_of_x_eq contact lastContact same)
    · exact (contacts_no_middle widthPositive heightPositive baseNotBottom baseNotTop firstContact lastContact contact ordered later).elim

end LeanTrominoes.RationalAffineBoundary
