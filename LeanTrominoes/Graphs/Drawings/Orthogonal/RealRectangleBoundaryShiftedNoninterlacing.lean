/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.RealRectangleBoundaryNoninterlacing

/-! # Noninterlacing straight chords in rectangles with arbitrary real origins -/
namespace LeanTrominoes.RealRectangleBoundary

def Port.shiftedPoint (origin : ℝ × ℝ) (width height : ℝ) (port : Port) : ℝ × ℝ :=
  (origin.1+(port.point width height).1,origin.2+(port.point width height).2)

theorem orientedArea_shiftedPoint (origin : ℝ × ℝ) (width height : ℝ) (first last point : Port) :
    GridSegment.orientedArea (first.shiftedPoint origin width height) (last.shiftedPoint origin width height)
      (point.shiftedPoint origin width height) =
    GridSegment.orientedArea (first.point width height) (last.point width height) (point.point width height) := by
  unfold GridSegment.orientedArea Port.shiftedPoint
  ring

theorem shifted_alternating_chords_interior_contact {origin : ℝ × ℝ} {width height : ℝ} {a b c d : Port} {first second : GridSegment}
    (widthPositive : 0 < width) (heightPositive : 0 < height)
    (aInside : a.Inside width height) (bInside : b.Inside width height)
    (cInside : c.Inside width height) (dInside : d.Inside width height)
    (acOrder : a.Before c) (cbOrder : c.Before b) (bdOrder : b.Before d)
    (firstSides : a.side ≠ b.side) (secondSides : c.side ≠ d.side)
    (firstStart : first.RealContains (a.shiftedPoint origin width height)) (firstEnd : first.RealContains (b.shiftedPoint origin width height))
    (secondStart : second.RealContains (c.shiftedPoint origin width height)) (secondEnd : second.RealContains (d.shiftedPoint origin width height)) :
    ∃ point : ℝ × ℝ, first.RealInteriorContains point ∧ second.RealInteriorContains point := by
  have abOrder : a.Before b := lt_trans acOrder cbOrder
  have cdOrder : c.Before d := lt_trans cbOrder bdOrder
  have cPositive := orientedArea_positive_between widthPositive heightPositive aInside cInside bInside acOrder cbOrder firstSides
  have dNegative := orientedArea_negative_outside widthPositive heightPositive aInside bInside dInside abOrder firstSides (Or.inr bdOrder)
  have aNegative := orientedArea_negative_outside widthPositive heightPositive cInside dInside aInside cdOrder secondSides (Or.inl acOrder)
  have bPositive := orientedArea_positive_between widthPositive heightPositive cInside bInside dInside cbOrder bdOrder secondSides
  have aPositive : 0 < GridSegment.orientedArea (d.point width height) (c.point width height) (a.point width height) := by
    unfold GridSegment.orientedArea at aNegative ⊢
    nlinarith
  have bNegative : GridSegment.orientedArea (d.point width height) (c.point width height) (b.point width height) < 0 := by
    unfold GridSegment.orientedArea at bPositive ⊢
    nlinarith
  apply GridSegment.real_interior_contact_of_opposite_sides firstStart firstEnd secondEnd secondStart
  all_goals rw [orientedArea_shiftedPoint]
  · exact dNegative
  · exact cPositive
  · exact aPositive
  · exact bNegative


theorem shifted_noninterlacing_of_disjoint_interiors {origin : ℝ × ℝ} {width height : ℝ} {a b c d : Port} {first second : GridSegment}
    (widthPositive : 0 < width) (heightPositive : 0 < height)
    (aInside : a.Inside width height) (bInside : b.Inside width height)
    (cInside : c.Inside width height) (dInside : d.Inside width height)
    (firstOrder : a.Before b) (secondOrder : c.Before d)
    (different : a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d)
    (firstSides : a.side ≠ b.side) (secondSides : c.side ≠ d.side)
    (firstStart : first.RealContains (a.shiftedPoint origin width height)) (firstEnd : first.RealContains (b.shiftedPoint origin width height))
    (secondStart : second.RealContains (c.shiftedPoint origin width height)) (secondEnd : second.RealContains (d.shiftedPoint origin width height))
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
        obtain ⟨point,firstInterior,secondInterior⟩ := shifted_alternating_chords_interior_contact widthPositive heightPositive
          aInside bInside cInside dInside acOrder cbOrder bdOrder firstSides secondSides firstStart firstEnd secondStart secondEnd
        exact False.elim (disjoint point firstInterior secondInterior)
  · by_cases daOrder : d.Before a
    · exact Or.inr (Or.inl daOrder)
    · have adOrder : a.Before d := lt_of_le_of_ne (le_of_not_gt daOrder) adDifferent
      by_cases bdOrder : b.Before d
      · exact Or.inr (Or.inr (Or.inr ⟨caOrder,bdOrder⟩))
      · have dbOrder : d.Before b := lt_of_le_of_ne (le_of_not_gt bdOrder) bdDifferent.symm
        obtain ⟨point,secondInterior,firstInterior⟩ := shifted_alternating_chords_interior_contact widthPositive heightPositive
          cInside dInside aInside bInside caOrder adOrder dbOrder secondSides firstSides secondStart secondEnd firstStart firstEnd
        exact False.elim (disjoint point firstInterior secondInterior)


end LeanTrominoes.RealRectangleBoundary
