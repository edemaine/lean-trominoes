/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.RealRectangleBoundaryCrossing

/-! # Disjoint straight boundary chords form a noninterlacing matching -/
namespace LeanTrominoes.RealRectangleBoundary

theorem Port.clockwiseCode_injective : Function.Injective Port.clockwiseCode := by
  intro first second equal
  have sideEq := congrArg (fun code => (ofLex code).1) equal
  have coordinateEq := congrArg (fun code => (ofLex code).2) equal
  obtain ⟨firstSide,firstCoordinate⟩ := first
  obtain ⟨secondSide,secondCoordinate⟩ := second
  have sides : firstSide = secondSide := Fin.ext sideEq
  subst secondSide
  have coordinates : firstCoordinate = secondCoordinate := by
    change (if firstSide.val < 2 then firstCoordinate else -firstCoordinate) =
      (if firstSide.val < 2 then secondCoordinate else -secondCoordinate) at coordinateEq
    split_ifs at coordinateEq <;> linarith
  subst secondCoordinate
  rfl

def Noninterlacing (a b c d : Port) : Prop :=
  b.Before c ∨ d.Before a ∨ (a.Before c ∧ d.Before b) ∨ (c.Before a ∧ b.Before d)

theorem noninterlacing_of_disjoint_interiors {width height : ℝ} {a b c d : Port} {first second : GridSegment}
    (widthPositive : 0 < width) (heightPositive : 0 < height)
    (aInside : a.Inside width height) (bInside : b.Inside width height)
    (cInside : c.Inside width height) (dInside : d.Inside width height)
    (firstOrder : a.Before b) (secondOrder : c.Before d)
    (different : a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d)
    (firstSides : a.side ≠ b.side) (secondSides : c.side ≠ d.side)
    (firstStart : first.RealContains (a.point width height)) (firstEnd : first.RealContains (b.point width height))
    (secondStart : second.RealContains (c.point width height)) (secondEnd : second.RealContains (d.point width height))
    (disjoint : ∀ point, first.RealInteriorContains point → second.RealInteriorContains point → False) :
    Noninterlacing a b c d := by
  have acDifferent : a.clockwiseCode ≠ c.clockwiseCode := fun equal => different.1 (Port.clockwiseCode_injective equal)
  have adDifferent : a.clockwiseCode ≠ d.clockwiseCode := fun equal => different.2.1 (Port.clockwiseCode_injective equal)
  have bcDifferent : b.clockwiseCode ≠ c.clockwiseCode := fun equal => different.2.2.1 (Port.clockwiseCode_injective equal)
  have bdDifferent : b.clockwiseCode ≠ d.clockwiseCode := fun equal => different.2.2.2 (Port.clockwiseCode_injective equal)
  rcases lt_or_gt_of_ne acDifferent with acOrder | caOrder
  · by_cases bcOrder : b.Before c
    · exact Or.inl bcOrder
    · have cbOrder : c.Before b := lt_of_le_of_ne (le_of_not_gt bcOrder) bcDifferent.symm
      by_cases dbOrder : d.Before b
      · exact Or.inr (Or.inr (Or.inl ⟨acOrder,dbOrder⟩))
      · have bdOrder : b.Before d := lt_of_le_of_ne (le_of_not_gt dbOrder) bdDifferent
        obtain ⟨point,firstInterior,secondInterior⟩ := alternating_chords_interior_contact widthPositive heightPositive
          aInside bInside cInside dInside acOrder cbOrder bdOrder firstSides secondSides firstStart firstEnd secondStart secondEnd
        exact False.elim (disjoint point firstInterior secondInterior)
  · by_cases daOrder : d.Before a
    · exact Or.inr (Or.inl daOrder)
    · have adOrder : a.Before d := lt_of_le_of_ne (le_of_not_gt daOrder) adDifferent
      by_cases bdOrder : b.Before d
      · exact Or.inr (Or.inr (Or.inr ⟨caOrder,bdOrder⟩))
      · have dbOrder : d.Before b := lt_of_le_of_ne (le_of_not_gt bdOrder) bdDifferent.symm
        obtain ⟨point,secondInterior,firstInterior⟩ := alternating_chords_interior_contact widthPositive heightPositive
          cInside dInside aInside bInside caOrder adOrder dbOrder secondSides firstSides secondStart secondEnd firstStart firstEnd
        exact False.elim (disjoint point firstInterior secondInterior)

end LeanTrominoes.RealRectangleBoundary
