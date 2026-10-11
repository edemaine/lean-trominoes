/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendSubdivisionVertexAvoidance
import LeanTrominoes.PeriodicGridDrawingRealAffineGeometry

/-! # A planar straight bookkeeping drawing for unperturbed bend subdivision

The auxiliary drawing has period `2M` and strict interior representatives.
It represents exactly the original polygonal geometry under one common
affine transformation. No geometric inward perturbation is needed.
-/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision

theorem shiftedDrawing_eq_affine {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing) :
    shiftedDrawing source drawing = (subdivisionDrawing source drawing).affine 2 (1,1) := by
  unfold shiftedDrawing PeriodicGridDrawing.affine
  congr 1
  · simp only [subdivisionDrawing,List.map_map,Function.comp_def]
    rfl
  · simp only [subdivisionDrawing,List.map_map,Function.comp_def,
      GridPolyline.affinePoints,PeriodicOrthocrossing.translatePolyline,scalePolyline]
    apply List.map_congr_left
    intro edge _
    simpa only [List.map_map,Function.comp_def,Nat.cast_ofNat] using shiftedRoute_affine source drawing edge

theorem shifted_planar {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) :
    (shiftedDrawing source drawing).IsRealPlanarDrawing (subdivisionGraph source drawing) := by
  refine ⟨⟨shifted_compatible planar,?_,?_⟩,?_⟩
  · rw [shiftedDrawing_eq_affine]
    exact (subdivision_routesSimple planar).affine (by decide) (1,1)
  · rw [shiftedDrawing_eq_affine]
    exact (subdivision_verticesAvoidRoutes planar).affine (by decide) (1,1)
  · rw [shiftedDrawing_eq_affine]
    exact (subdivision_routesMeetOnlyAtEndpoints planar).affine (by decide) (1,1)

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
