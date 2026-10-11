/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendVerticalFanPlacement
import LeanTrominoes.GridPolylineRealEndpointContainment

/-! # Placed incidence fans meet only at their common vertex

In particular, a fan cannot pass through another incidence's anchor.
-/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem fanAnchor_ne_zero {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    {port : GraphPort (Vertex V)} (member : port ∈ allPorts (subdivisionGraph source drawing)) :
    fanAnchor source drawing port ≠ (0,0) := by
  intro zero
  have x := fanAnchor_x planar degree member
  cases key : (shiftedDrawing source drawing).portRayKey port with
  | right slope => simp [zero,key,BendFan.horizontalSign] at x
  | left slope => simp [zero,key,BendFan.horizontalSign] at x
  | up => have y := fanAnchor_vertical_y planar degree member true key; simp [zero] at y
  | down => have y := fanAnchor_vertical_y planar degree member false key; simp [zero] at y

theorem fanAt_contact_center {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    (factor : Int) {raster : Nat} (positive : 0 < raster) (center : Cell)
    {first second : GraphPort (Vertex V)}
    (firstMember : first ∈ allPorts (subdivisionGraph source drawing))
    (secondMember : second ∈ allPorts (subdivisionGraph source drawing))
    (sameVertex : first.vertex = second.vertex) (different : first ≠ second) {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (fanAt source drawing factor raster center first) point)
    (secondContains : GridPolyline.RealContains (fanAt source drawing factor raster center second) point) :
    point = realCell (Cell.scale ((raster : Int)*factor) center) := by
  have nonzero : (raster : Int) ≠ 0 := by exact_mod_cast positive.ne'
  have realNonzero : (raster : ℝ) ≠ 0 := by exact_mod_cast positive.ne'
  have firstShifted := (GridPolyline.realContains_translate_inverse _ _ _).mp firstContains
  have secondShifted := (GridPolyline.realContains_translate_inverse _ _ _).mp secondContains
  have firstRaw := (GridPolyline.realContains_scale_inverse _ nonzero _).mp firstShifted
  have secondRaw := (GridPolyline.realContains_scale_inverse _ nonzero _).mp secondShifted
  have contact := fanRoutes_contact planar degree firstMember secondMember sameVertex different firstRaw secondRaw
  apply Prod.ext
  · have x := congrArg Prod.fst contact
    simp only [realCell] at x ⊢
    have difference := (div_eq_iff realNonzero).mp x
    norm_num only [Int.cast_zero,zero_mul] at difference
    linarith
  · have y := congrArg Prod.snd contact
    simp only [realCell] at y ⊢
    have difference := (div_eq_iff realNonzero).mp y
    norm_num only [Int.cast_zero,zero_mul] at difference
    linarith

theorem fanAt_avoids_other_anchor {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    (factor : Int) {raster : Nat} (positive : 0 < raster) (center : Cell)
    {first second : GraphPort (Vertex V)}
    (firstMember : first ∈ allPorts (subdivisionGraph source drawing))
    (secondMember : second ∈ allPorts (subdivisionGraph source drawing))
    (sameVertex : first.vertex = second.vertex) (different : first ≠ second) :
    ¬GridPolyline.RealContains (fanAt source drawing factor raster center second)
      (realCell (Cell.add (Cell.scale ((raster : Int)*factor) center) (Cell.scale raster (fanAnchor source drawing first)))) := by
  intro contains
  have ownContains := GridPolyline.realContains_last (fanAt_simple planar factor positive center firstMember).1
    (fanAt_last source drawing factor raster center first)
  have contact := fanAt_contact_center planar degree factor positive center firstMember secondMember sameVertex different ownContains contains
  have x := congrArg Prod.fst contact
  have y := congrArg Prod.snd contact
  have nonzero : (raster : ℝ) ≠ 0 := by exact_mod_cast positive.ne'
  simp only [realCell,Cell.add,Cell.scale,Int.cast_add,Int.cast_mul,Int.cast_natCast] at x y
  have anchorZero : fanAnchor source drawing first = (0,0) := by
    apply Prod.ext
    · have multiplied : (raster : ℝ)*(fanAnchor source drawing first).1 = 0 := by linarith
      have zero := (mul_eq_zero.mp multiplied).resolve_left nonzero
      exact_mod_cast zero
    · have multiplied : (raster : ℝ)*(fanAnchor source drawing first).2 = 0 := by linarith
      have zero := (mul_eq_zero.mp multiplied).resolve_left nonzero
      exact_mod_cast zero
  exact fanAnchor_ne_zero planar degree firstMember anchorZero

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
