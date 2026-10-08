/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.RationalAffineBoundaryContacts

/-! # A rational line with a proper rectangle contact has two distinct contacts -/
namespace LeanTrominoes.RationalAffineBoundary

theorem contact_after_left {width height base slope : ℚ} (widthPositive : 0 < width)
    (firstInside : 0 < base ∧ base < height) (lastNotBottom : base+slope*width ≠ 0)
    (lastNotTop : base+slope*width ≠ height) :
    ∃ point, Contact width height base slope point ∧ 0 < point.1 := by
  by_cases lastPositive : 0 < base+slope*width
  · by_cases lastBelow : base+slope*width < height
    · refine ⟨(width,base+slope*width),?_,widthPositive⟩
      exact ⟨rfl,Or.inl ⟨Or.inr rfl,lastPositive,lastBelow⟩⟩
    · have above : height < base+slope*width := lt_of_le_of_ne (le_of_not_gt lastBelow) lastNotTop.symm
      obtain ⟨x,lo,hi,equal⟩ := affine_intermediate widthPositive (Or.inl ⟨by simpa using firstInside.2,above⟩)
      exact ⟨(x,height),⟨equal.symm,Or.inr ⟨Or.inr rfl,lo,hi⟩⟩,lo⟩
  · have below : base+slope*width < 0 := lt_of_le_of_ne (le_of_not_gt lastPositive) lastNotBottom
    obtain ⟨x,lo,hi,equal⟩ := affine_intermediate widthPositive (Or.inr ⟨below,by simpa using firstInside.1⟩)
    exact ⟨(x,0),⟨equal.symm,Or.inr ⟨Or.inl rfl,lo,hi⟩⟩,lo⟩

theorem contact_before_right {width height base slope : ℚ} (widthPositive : 0 < width)
    (lastInside : 0 < base+slope*width ∧ base+slope*width < height) (firstNotBottom : base ≠ 0)
    (firstNotTop : base ≠ height) :
    ∃ point, Contact width height base slope point ∧ point.1 < width := by
  by_cases firstPositive : 0 < base
  · by_cases firstBelow : base < height
    · refine ⟨(0,base),?_,widthPositive⟩
      exact ⟨by simp,Or.inl ⟨Or.inl rfl,firstPositive,firstBelow⟩⟩
    · have above : height < base := lt_of_le_of_ne (le_of_not_gt firstBelow) firstNotTop.symm
      obtain ⟨x,lo,hi,equal⟩ := affine_intermediate widthPositive (Or.inr ⟨lastInside.2,by simpa using above⟩)
      exact ⟨(x,height),⟨equal.symm,Or.inr ⟨Or.inr rfl,lo,hi⟩⟩,hi⟩
  · have below : base < 0 := lt_of_le_of_ne (le_of_not_gt firstPositive) firstNotBottom
    obtain ⟨x,lo,hi,equal⟩ := affine_intermediate widthPositive (Or.inl ⟨by simpa using below,lastInside.1⟩)
    exact ⟨(x,0),⟨equal.symm,Or.inr ⟨Or.inl rfl,lo,hi⟩⟩,hi⟩

theorem endpoint_cases_of_contact {width height base slope : ℚ} {point : ℚ × ℚ}
    (widthPositive : 0 < width) (heightPositive : 0 < height)
    (firstNotBottom : base ≠ 0) (firstNotTop : base ≠ height)
    (lastNotBottom : base+slope*width ≠ 0) (lastNotTop : base+slope*width ≠ height)
    (contact : Contact width height base slope point) :
    (0 < base ∧ base < height) ∨ (0 < base+slope*width ∧ base+slope*width < height) ∨
      (base < 0 ∧ height < base+slope*width) ∨ (base+slope*width < 0 ∧ height < base) := by
  have coordinateBounds : 0 ≤ point.1 ∧ point.1 ≤ width := by
    rcases contact.2 with vertical | horizontal
    · rcases vertical.1 with equal | equal <;> rw [equal] <;> exact ⟨by linarith,by linarith⟩
    · exact ⟨horizontal.2.1.le,horizontal.2.2.le⟩
  have heightBounds : 0 ≤ point.2 ∧ point.2 ≤ height := by
    rcases contact.2 with vertical | horizontal
    · exact ⟨vertical.2.1.le,vertical.2.2.le⟩
    · rcases horizontal.1 with equal | equal <;> rw [equal] <;> exact ⟨by linarith,by linarith⟩
  rw [contact.1] at heightBounds
  have interval := affine_value_between_endpoints (base := base) (slope := slope) coordinateBounds
  rcases le_total base (base+slope*width) with increasing | decreasing
  · simp only [min_eq_left increasing,max_eq_right increasing] at interval
    have lo : 0 < base+slope*width := lt_of_le_of_ne (by linarith [interval.2,heightBounds.1]) lastNotBottom.symm
    have hi : base < height := lt_of_le_of_ne (by linarith [interval.1,heightBounds.2]) firstNotTop
    by_cases firstPositive : 0 < base
    · exact Or.inl ⟨firstPositive,hi⟩
    · by_cases lastBelow : base+slope*width < height
      · exact Or.inr (Or.inl ⟨lo,lastBelow⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨lt_of_le_of_ne (le_of_not_gt firstPositive) firstNotBottom,
          lt_of_le_of_ne (le_of_not_gt lastBelow) lastNotTop.symm⟩))
  · simp only [min_eq_right decreasing,max_eq_left decreasing] at interval
    have lo : 0 < base := lt_of_le_of_ne (by linarith [interval.2,heightBounds.1]) firstNotBottom.symm
    have hi : base+slope*width < height := lt_of_le_of_ne (by linarith [interval.1,heightBounds.2]) lastNotTop
    by_cases lastPositive : 0 < base+slope*width
    · exact Or.inr (Or.inl ⟨lastPositive,hi⟩)
    · by_cases firstBelow : base < height
      · exact Or.inl ⟨lo,firstBelow⟩
      · exact Or.inr (Or.inr (Or.inr ⟨lt_of_le_of_ne (le_of_not_gt lastPositive) lastNotBottom,
          lt_of_le_of_ne (le_of_not_gt firstBelow) firstNotTop.symm⟩))

theorem two_distinct_contacts {width height base slope : ℚ} {point : ℚ × ℚ}
    (widthPositive : 0 < width) (heightPositive : 0 < height)
    (firstNotBottom : base ≠ 0) (firstNotTop : base ≠ height)
    (lastNotBottom : base+slope*width ≠ 0) (lastNotTop : base+slope*width ≠ height)
    (contact : Contact width height base slope point) :
    ∃ first last, Contact width height base slope first ∧ Contact width height base slope last ∧ first ≠ last := by
  rcases endpoint_cases_of_contact widthPositive heightPositive firstNotBottom firstNotTop lastNotBottom lastNotTop contact with
    firstInside | lastInside | increasing | decreasing
  · obtain ⟨last,lastContact,positiveX⟩ := contact_after_left widthPositive firstInside lastNotBottom lastNotTop
    refine ⟨(0,base),last,⟨by simp,Or.inl ⟨Or.inl rfl,firstInside⟩⟩,lastContact,?_⟩
    intro equal
    have equalX := congrArg Prod.fst equal
    dsimp only at equalX
    linarith
  · obtain ⟨first,firstContact,upperX⟩ := contact_before_right widthPositive lastInside firstNotBottom firstNotTop
    refine ⟨first,(width,base+slope*width),firstContact,⟨rfl,Or.inl ⟨Or.inr rfl,lastInside⟩⟩,?_⟩
    intro equal
    have equalX := congrArg Prod.fst equal
    dsimp only at equalX
    linarith
  · obtain ⟨bottom,bl,bh,be⟩ := affine_intermediate widthPositive (Or.inl ⟨by simpa using increasing.1,by linarith [increasing.2]⟩)
    obtain ⟨top,tl,th,te⟩ := affine_intermediate widthPositive (Or.inl ⟨by simpa using (increasing.1.trans heightPositive),increasing.2⟩)
    refine ⟨(bottom,0),(top,height),⟨be.symm,Or.inr ⟨Or.inl rfl,bl,bh⟩⟩,⟨te.symm,Or.inr ⟨Or.inr rfl,tl,th⟩⟩,?_⟩
    intro equal
    have equalY := congrArg Prod.snd equal
    dsimp only at equalY
    linarith
  · obtain ⟨bottom,bl,bh,be⟩ := affine_intermediate widthPositive (Or.inr ⟨decreasing.1,by simpa using (heightPositive.trans decreasing.2)⟩)
    obtain ⟨top,tl,th,te⟩ := affine_intermediate (base := base) (slope := slope) (value := height)
      widthPositive (Or.inr ⟨by linarith [decreasing.1],by simpa using decreasing.2⟩)
    refine ⟨(bottom,0),(top,height),⟨be.symm,Or.inr ⟨Or.inl rfl,bl,bh⟩⟩,⟨te.symm,Or.inr ⟨Or.inr rfl,tl,th⟩⟩,?_⟩
    intro equal
    have equalY := congrArg Prod.snd equal
    dsimp only at equalY
    linarith

end LeanTrominoes.RationalAffineBoundary
