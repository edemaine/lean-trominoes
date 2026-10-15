/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.RealRectangleBoundaryOrientation

/-! # Alternating straight boundary chords intersect in their interiors -/
namespace LeanTrominoes.RealRectangleBoundary

theorem Port.before_side_le {first last : Port} (ordered : first.Before last) : first.side.val ≤ last.side.val := by
  simp only [Before,clockwiseCode,Prod.Lex.toLex_lt_toLex] at ordered
  rcases ordered with less | ⟨same,_⟩ <;> omega

theorem Port.before_side_lt {first last : Port} (ordered : first.Before last) (different : first.side ≠ last.side) :
    first.side.val < last.side.val := by
  have le := before_side_le ordered
  have ne : first.side.val ≠ last.side.val := fun equal => different (Fin.ext equal)
  omega

theorem orientedArea_negative_outside {width height : ℝ} {first last point : Port}
    (widthPositive : 0 < width) (heightPositive : 0 < height)
    (firstInside : first.Inside width height) (lastInside : last.Inside width height)
    (pointInside : point.Inside width height) (ordered : first.Before last)
    (differentSides : first.side ≠ last.side) (outside : point.Before first ∨ last.Before point) :
    GridSegment.orientedArea (first.point width height) (last.point width height) (point.point width height) < 0 := by
  rcases outside with before | after
  · have sidesDifferent : point.side ≠ last.side := by
      have firstLess := Port.before_side_lt ordered differentSides
      have pointLe := Port.before_side_le before
      intro same
      have values := congrArg Fin.val same
      omega
    have positive := orientedArea_positive_between widthPositive heightPositive pointInside firstInside lastInside
      before ordered sidesDifferent
    have negativeEq : GridSegment.orientedArea (first.point width height) (last.point width height) (point.point width height) =
        -GridSegment.orientedArea (point.point width height) (last.point width height) (first.point width height) := by
      unfold GridSegment.orientedArea
      ring
    rw [negativeEq]
    exact neg_neg_of_pos positive
  · have sidesDifferent : first.side ≠ point.side := by
      have firstLess := Port.before_side_lt ordered differentSides
      have pointLe := Port.before_side_le after
      intro same
      have values := congrArg Fin.val same
      omega
    have positive := orientedArea_positive_between widthPositive heightPositive firstInside lastInside pointInside
      ordered after sidesDifferent
    have negativeEq : GridSegment.orientedArea (first.point width height) (last.point width height) (point.point width height) =
        -GridSegment.orientedArea (first.point width height) (point.point width height) (last.point width height) := by
      unfold GridSegment.orientedArea
      ring
    rw [negativeEq]
    exact neg_neg_of_pos positive

theorem alternating_chords_interior_contact {width height : ℝ} {a b c d : Port} {first second : GridSegment}
    (widthPositive : 0 < width) (heightPositive : 0 < height)
    (aInside : a.Inside width height) (bInside : b.Inside width height)
    (cInside : c.Inside width height) (dInside : d.Inside width height)
    (acOrder : a.Before c) (cbOrder : c.Before b) (bdOrder : b.Before d)
    (firstSides : a.side ≠ b.side) (secondSides : c.side ≠ d.side)
    (firstStart : first.RealContains (a.point width height)) (firstEnd : first.RealContains (b.point width height))
    (secondStart : second.RealContains (c.point width height)) (secondEnd : second.RealContains (d.point width height)) :
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
  exact GridSegment.real_interior_contact_of_opposite_sides firstStart firstEnd secondEnd secondStart
    dNegative cPositive aPositive bNegative

end LeanTrominoes.RealRectangleBoundary
