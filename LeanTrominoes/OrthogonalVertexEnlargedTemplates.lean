/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.OrthogonalVertexAnchorTemplateGeometry
import LeanTrominoes.GridPolylineRealOpenScaling
import LeanTrominoes.OrthogonalPolylineScaling
import LeanTrominoes.OrthogonalPolylineSymmetries

/-! # Enlarged rectangle connectors retain simplicity and isolation -/
namespace LeanTrominoes.OrthogonalDrawingRefinement
open PeriodicOrthocrossing

def enlargedRectangleTemplate (factor : Int) (radius : Nat) (position : Cell) (profile : AnchorProfile) (index : Fin 4) : List Cell :=
  translatePolyline (Cell.scale factor position) (scalePolyline radius (rectangleTemplate profile index))

theorem enlargedRectangleTemplate_isRealOpenSimple (factor : Int) {radius : Nat} (positive : 0 < radius)
    (position : Cell) (profile : AnchorProfile) (index : Fin 4) :
    GridPolyline.IsRealOpenSimple (enlargedRectangleTemplate factor radius position profile index) :=
  ((rectangleTemplate_isRealOpenSimple profile index).scale (by exact_mod_cast positive.ne')).translate _

theorem enlargedRectangleTemplate_orthogonal (factor : Int) {radius : Nat} (positive : 0 < radius)
    (position : Cell) (profile : AnchorProfile) (index : Fin 4) :
    OrthogonalPolyline (enlargedRectangleTemplate factor radius position profile index) :=
  ((rectangleTemplate_orthogonal profile index).scalePolyline positive).translate _

theorem enlargedRectangleTemplate_real_bounds (factor : Int) (radius : Nat) (position : Cell) (profile : AnchorProfile) (index : Fin 4)
    {point : ℝ × ℝ} (contains : GridPolyline.RealContains (enlargedRectangleTemplate factor radius position profile index) point) :
    |point.1-(factor : ℝ)*position.1| ≤ 5*(radius : ℝ) ∧ |point.2-(factor : ℝ)*position.2| ≤ 10*(radius : ℝ) := by
  have original := (GridPolyline.realContains_translate_inverse _ _ _).mp contains
  have vertices : ∀ vertex ∈ scalePolyline radius (rectangleTemplate profile index),
      -5*(radius : Int) ≤ vertex.1 ∧ vertex.1 ≤ 5*radius ∧ -10*(radius : Int) ≤ vertex.2 ∧ vertex.2 ≤ 10*radius := by
    intro vertex member
    change vertex ∈ (rectangleTemplate profile index).map (Cell.scale radius) at member
    obtain ⟨old,oldMember,rfl⟩ := List.mem_map.mp member
    have bounds := rectangleTemplate_points_in_rectangle profile index old oldMember
    have nonnegative : (0 : Int) ≤ radius := by positivity
    simp only [Cell.scale]
    exact ⟨by nlinarith [bounds.1],by nlinarith [bounds.2.1],by nlinarith [bounds.2.2.1],by nlinarith [bounds.2.2.2]⟩
  have bounds := GridPolyline.realContains_bounds vertices original
  simp only [Cell.scale,Prod.fst,Prod.snd,Int.cast_mul] at bounds
  norm_num only [Int.cast_neg,Int.cast_ofNat,Int.cast_natCast] at bounds
  exact ⟨abs_le.mpr ⟨by linarith [bounds.1],by linarith [bounds.2.1]⟩,
    abs_le.mpr ⟨by linarith [bounds.2.2.1],by linarith [bounds.2.2.2]⟩⟩

theorem enlargedRectangleTemplate_contacts_same_position {factor : Int} {radius : Nat}
    (spacing : 20*(radius : Int) < factor)
    {firstPosition secondPosition : Cell} (firstProfile secondProfile : AnchorProfile) (first second : Fin 4)
    {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (enlargedRectangleTemplate factor radius firstPosition firstProfile first) point)
    (secondContains : GridPolyline.RealContains (enlargedRectangleTemplate factor radius secondPosition secondProfile second) point) :
    firstPosition = secondPosition := by
  have fb := enlargedRectangleTemplate_real_bounds factor radius firstPosition firstProfile first firstContains
  have sb := enlargedRectangleTemplate_real_bounds factor radius secondPosition secondProfile second secondContains
  have radiusNonnegative : (0 : Int) ≤ radius := by positivity
  apply Prod.ext
  · apply GridSegment.closed_interval_periodic_shifts_unique (period := factor) (lower := -5*(radius : Int)) (upper := 5*radius)
      (point := point.1) (by omega) (by omega)
    all_goals
      push_cast
      constructor <;> linarith [(abs_le.mp fb.1).1,(abs_le.mp fb.1).2,(abs_le.mp sb.1).1,(abs_le.mp sb.1).2]
  · apply GridSegment.closed_interval_periodic_shifts_unique (period := factor) (lower := -10*(radius : Int)) (upper := 10*radius)
      (point := point.2) (by omega) (by omega)
    all_goals
      push_cast
      constructor <;> linarith [(abs_le.mp fb.2).1,(abs_le.mp fb.2).2,(abs_le.mp sb.2).1,(abs_le.mp sb.2).2]

theorem enlargedRectangleTemplate_contacts_center (factor : Int) {radius : Nat} (positive : 0 < radius)
    (position : Cell) (profile : AnchorProfile) (first second : Fin 4)
    (degree : profile.degree ≤ 4) (firstValid : first.val < profile.degree) (secondValid : second.val < profile.degree)
    (different : first ≠ second) {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (enlargedRectangleTemplate factor radius position profile first) point)
    (secondContains : GridPolyline.RealContains (enlargedRectangleTemplate factor radius position profile second) point) :
    point = realCell (Cell.scale factor position) := by
  have nonzero : (radius : Int) ≠ 0 := by exact_mod_cast positive.ne'
  have realNonzero : (radius : ℝ) ≠ 0 := by exact_mod_cast positive.ne'
  have firstOriginal := (GridPolyline.realContains_scale_inverse _ nonzero _).mp
    ((GridPolyline.realContains_translate_inverse _ _ _).mp firstContains)
  have secondOriginal := (GridPolyline.realContains_scale_inverse _ nonzero _).mp
    ((GridPolyline.realContains_translate_inverse _ _ _).mp secondContains)
  have center := rectangleTemplate_contacts_center profile first second degree firstValid secondValid different firstOriginal secondOriginal
  have x := congrArg Prod.fst center
  have y := congrArg Prod.snd center
  norm_num only [realCell,Prod.fst,Prod.snd,Int.cast_zero,Int.cast_natCast] at x y
  have xZero := (div_eq_iff realNonzero).mp x
  have yZero := (div_eq_iff realNonzero).mp y
  apply Prod.ext <;> simp only [realCell,Prod.fst,Prod.snd] <;> linarith

end LeanTrominoes.OrthogonalDrawingRefinement
