/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingRawBendVerticalFanGeometry
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingRawBendFanPlacement

/-! # Vertical boundary contacts after fan placement and raster scaling -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem fanAt_vertical_boundary_contact {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    (factor : Int) {raster : Nat} (positive : 0 < raster) (center : Cell)
    {port : GraphPort (Vertex V)} (member : port ∈ allPorts (subdivisionGraph source drawing))
    (north : Bool) {point : ℝ × ℝ} (contains : GridPolyline.RealContains (fanAt source drawing factor raster center port) point)
    (height : point.2 = (raster : ℝ)*factor*center.2+(raster : ℝ)*(if north then 10 else -10)) :
    point = realCell (Cell.add (Cell.scale ((raster : Int)*factor) center) (Cell.scale raster (fanAnchor source drawing port))) := by
  have nonzero : (raster : Int) ≠ 0 := by exact_mod_cast positive.ne'
  have realNonzero : (raster : ℝ) ≠ 0 := by exact_mod_cast positive.ne'
  have shifted := (GridPolyline.realContains_translate_inverse _ _ _).mp contains
  have raw := (GridPolyline.realContains_scale_inverse _ nonzero _).mp shifted
  have rawHeight : (point.2-(Cell.scale ((raster : Int)*factor) center).2)/(raster : ℝ) = if north then 10 else -10 := by
    apply (div_eq_iff realNonzero).mpr
    simp only [Cell.scale,Int.cast_mul,Int.cast_natCast]
    cases north <;> norm_num at height ⊢ <;> nlinarith
  have contact := fanRoute_vertical_boundary_contact planar degree member north raw rawHeight
  have x := (div_eq_iff realNonzero).mp (congrArg Prod.fst contact)
  have y := (div_eq_iff realNonzero).mp (congrArg Prod.snd contact)
  apply Prod.ext
  · simp only [realCell,Cell.scale,Cell.add,Int.cast_mul,Int.cast_add,Int.cast_natCast] at x ⊢
    nlinarith
  · simp only [realCell,Cell.scale,Cell.add,Int.cast_mul,Int.cast_add,Int.cast_natCast] at y ⊢
    nlinarith

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
