/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.OrthogonalBoundaryArcRouting
import Mathlib.Data.Prod.Lex

/-! # A linear order for rectangle boundary ports with a fixed corner cut -/
namespace LeanTrominoes.OrthogonalBoundaryRouting

def Port.clockwiseCode (port : Port) : Nat ×ₗ Int :=
  toLex (port.side.val,if port.side.val < 2 then port.coordinate else -port.coordinate)

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
    split_ifs at coordinateEq <;> omega
  subst secondCoordinate
  rfl

theorem Port.before_iff_code_lt (first second : Port) :
    first.Before second ↔ first.clockwiseCode < second.clockwiseCode := by
  simp only [Before,clockwiseCode,Prod.Lex.toLex_lt_toLex]
  constructor
  · rintro (order | ⟨same,order⟩)
    · exact Or.inl order
    · right
      refine ⟨congrArg Fin.val same,?_⟩
      rw [same] at order ⊢
      split_ifs at order ⊢ <;> omega
  · rintro (order | ⟨same,order⟩)
    · exact Or.inl order
    · right
      have sides : first.side = second.side := Fin.ext same
      refine ⟨sides,?_⟩
      rw [sides] at order ⊢
      split_ifs at order ⊢ <;> omega

theorem Port.before_trans {first second third : Port}
    (firstOrder : first.Before second) (secondOrder : second.Before third) : first.Before third :=
  (before_iff_code_lt _ _).mpr
    (((before_iff_code_lt _ _).mp firstOrder).trans ((before_iff_code_lt _ _).mp secondOrder))

theorem Port.not_before_self (port : Port) : ¬port.Before port := by
  rw [before_iff_code_lt]
  exact lt_irrefl _

theorem Port.before_ne {first second : Port} (order : first.Before second) : first ≠ second := by
  intro same
  subst second
  exact first.not_before_self order

def Port.Between (first last point : Port) : Prop :=
  (first = point ∨ first.Before point) ∧ (point = last ∨ point.Before last)

theorem Port.between_iff_code_le (first last point : Port) :
    first.Between last point ↔ first.clockwiseCode ≤ point.clockwiseCode ∧
      point.clockwiseCode ≤ last.clockwiseCode := by
  simp only [Between,before_iff_code_lt,le_iff_eq_or_lt]
  constructor
  · rintro ⟨left,right⟩
    exact ⟨left.imp (congrArg clockwiseCode) id,right.imp (congrArg clockwiseCode) id⟩
  · rintro ⟨left,right⟩
    exact ⟨left.imp (fun equal => clockwiseCode_injective equal) id,
      right.imp (fun equal => clockwiseCode_injective equal) id⟩

end LeanTrominoes.OrthogonalBoundaryRouting
