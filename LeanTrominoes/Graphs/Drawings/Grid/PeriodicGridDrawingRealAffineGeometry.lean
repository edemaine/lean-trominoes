/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridPolylineRealAffineSimplicity
import LeanTrominoes.Common.Geometry.GridPolylineRealEndpointAffine

/-! # Positive affine transformations preserve periodic real geometry

The geometric transport theorems do not require strict interior vertex
representatives. This permits a raw subdivision with boundary bends to use
a translated bookkeeping drawing for port assignment.
-/
namespace LeanTrominoes
open PeriodicOrthocrossing

namespace GridPolyline

def affinePoints (factor : Int) (shift : Cell) (route : List Cell) : List Cell :=
  translatePolyline shift (scalePolyline factor route)

noncomputable def affineRealPoint (factor : Int) (shift : Cell) (point : ℝ × ℝ) : ℝ × ℝ :=
  (shift.1+(factor : ℝ)*point.1,shift.2+(factor : ℝ)*point.2)

noncomputable def inverseAffineRealPoint (factor : Int) (shift : Cell) (point : ℝ × ℝ) : ℝ × ℝ :=
  ((point.1-shift.1)/(factor : ℝ),(point.2-shift.2)/(factor : ℝ))

theorem affineRealPoint_cell (factor : Int) (shift point : Cell) :
    affineRealPoint factor shift (realCell point) = realCell (Cell.add shift (Cell.scale factor point)) := by
  simp [affineRealPoint,realCell,Cell.add,Cell.scale]

theorem affine_inverse_point {factor : Int} (nonzero : factor ≠ 0) (shift : Cell) (point : ℝ × ℝ) :
    affineRealPoint factor shift (inverseAffineRealPoint factor shift point) = point := by
  have realNonzero : (factor : ℝ) ≠ 0 := by exact_mod_cast nonzero
  simp [affineRealPoint,inverseAffineRealPoint,mul_div_cancel₀ _ realNonzero]

theorem inverse_affine_point {factor : Int} (nonzero : factor ≠ 0) (shift : Cell) (point : ℝ × ℝ) :
    inverseAffineRealPoint factor shift (affineRealPoint factor shift point) = point := by
  have realNonzero : (factor : ℝ) ≠ 0 := by exact_mod_cast nonzero
  simp [affineRealPoint,inverseAffineRealPoint,realNonzero]

theorem realContains_affine_inverse (route : List Cell) {factor : Int} (nonzero : factor ≠ 0)
    (shift : Cell) (point : ℝ × ℝ) :
    RealContains (affinePoints factor shift route) point ↔ RealContains route (inverseAffineRealPoint factor shift point) := by
  rw [affinePoints,realContains_translate_inverse,realContains_scale_inverse _ nonzero]
  rfl

theorem realContains_affine (route : List Cell) {factor : Int} (nonzero : factor ≠ 0)
    (shift : Cell) (point : ℝ × ℝ) :
    RealContains (affinePoints factor shift route) (affineRealPoint factor shift point) ↔ RealContains route point := by
  rw [realContains_affine_inverse _ nonzero,inverse_affine_point nonzero]

theorem RealIsEndpoint.affine {route : List Cell} {point : ℝ × ℝ} (endpoint : RealIsEndpoint route point)
    (factor : Int) (shift : Cell) :
    RealIsEndpoint (affinePoints factor shift route) (affineRealPoint factor shift point) :=
  (endpoint.scale factor).translate shift

theorem IsRealSimple.affine {route : List Cell} (simple : IsRealSimple route) {factor : Int}
    (nonzero : factor ≠ 0) (shift : Cell) : IsRealSimple (affinePoints factor shift route) :=
  (simple.scale nonzero).translate shift

end GridPolyline

namespace PeriodicGridDrawing

def affine (drawing : PeriodicGridDrawing) (factor : Nat) (shift : Cell) : PeriodicGridDrawing where
  gridSizePred := factor*drawing.gridSize-1
  vertexPositions := drawing.vertexPositions.map (fun point => Cell.add shift (Cell.scale factor point))
  edgeRoutes := drawing.edgeRoutes.map (GridPolyline.affinePoints factor shift)

theorem affine_gridSize (drawing : PeriodicGridDrawing) {factor : Nat} (positive : 0 < factor) (shift : Cell) :
    (drawing.affine factor shift).gridSize = factor*drawing.gridSize := by
  change factor*drawing.gridSize-1+1 = factor*drawing.gridSize
  exact Nat.sub_add_cancel (Nat.mul_pos positive (Nat.zero_lt_succ drawing.gridSizePred))

theorem affine_edgeRoute (drawing : PeriodicGridDrawing) (factor : Nat) (shift : Cell) {index : Nat}
    (valid : index < drawing.edgeRoutes.length) :
    (drawing.affine factor shift).edgeRoute index = GridPolyline.affinePoints factor shift (drawing.edgeRoute index) := by
  simp only [affine,edgeRoute]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using valid),List.getElem_map,List.getD_eq_getElem _ _ valid]

theorem affine_realEdgeRoute (drawing : PeriodicGridDrawing) {factor : Nat} (positive : 0 < factor) (shift : Cell)
    {index : Nat} (valid : index < drawing.edgeRoutes.length) (cell : Cell) :
    (drawing.affine factor shift).realEdgeRoute index cell =
      GridPolyline.affinePoints factor shift (drawing.realEdgeRoute index cell) := by
  simp only [realEdgeRoute,affine_edgeRoute drawing factor shift valid,GridPolyline.affinePoints,
    translatePolyline,scalePolyline,List.map_map,Function.comp_def,periodTranslation,affine_gridSize drawing positive,Nat.cast_mul]
  apply List.map_congr_left
  intro point _
  apply Prod.ext <;> dsimp [Cell.add,Cell.scale] <;> ring

theorem affine_lift_vertex (drawing : PeriodicGridDrawing) {factor : Nat} (positive : 0 < factor)
    (shift vertex cell : Cell) :
    Cell.add (Cell.add shift (Cell.scale factor vertex)) ((drawing.affine factor shift).periodTranslation cell) =
      Cell.add shift (Cell.scale factor (Cell.add vertex (drawing.periodTranslation cell))) := by
  simp only [periodTranslation,affine_gridSize drawing positive,Nat.cast_mul]
  apply Prod.ext <;> dsimp [Cell.add,Cell.scale] <;> ring

theorem RealRoutesAreSimple.affine {drawing : PeriodicGridDrawing} (simple : drawing.RealRoutesAreSimple)
    {factor : Nat} (positive : 0 < factor) (shift : Cell) : (drawing.affine factor shift).RealRoutesAreSimple := by
  intro route member
  obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
  exact (simple original originalMember).affine (by exact_mod_cast ne_of_gt positive) shift

theorem RealVerticesAvoidRoutes.affine {drawing : PeriodicGridDrawing} (avoids : drawing.RealVerticesAvoidRoutes)
    {factor : Nat} (positive : 0 < factor) (shift : Cell) : (drawing.affine factor shift).RealVerticesAvoidRoutes := by
  intro vertex member vertexCell edgeCell edgeIndex edgeValid contains
  have valid : edgeIndex < drawing.edgeRoutes.length := by simpa only [PeriodicGridDrawing.affine,List.length_map] using edgeValid
  obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
  rw [affine_realEdgeRoute drawing positive shift valid,affine_lift_vertex drawing positive] at contains ⊢
  rw [← GridPolyline.affineRealPoint_cell] at contains ⊢
  have oldContains := (GridPolyline.realContains_affine _ (by exact_mod_cast ne_of_gt positive) shift _).mp contains
  exact (avoids original originalMember vertexCell edgeCell edgeIndex valid oldContains).affine factor shift

theorem RealRoutesMeetOnlyAtEndpoints.affine {drawing : PeriodicGridDrawing}
    (contacts : drawing.RealRoutesMeetOnlyAtEndpoints) {factor : Nat} (positive : 0 < factor) (shift : Cell) :
    (drawing.affine factor shift).RealRoutesMeetOnlyAtEndpoints := by
  intro firstIndex secondIndex firstCell secondCell firstValid secondValid different point firstContains secondContains
  have firstValid' : firstIndex < drawing.edgeRoutes.length := by simpa only [PeriodicGridDrawing.affine,List.length_map] using firstValid
  have secondValid' : secondIndex < drawing.edgeRoutes.length := by simpa only [PeriodicGridDrawing.affine,List.length_map] using secondValid
  rw [affine_realEdgeRoute drawing positive shift firstValid'] at firstContains ⊢
  rw [affine_realEdgeRoute drawing positive shift secondValid'] at secondContains ⊢
  have nonzero : (factor : Int) ≠ 0 := by exact_mod_cast ne_of_gt positive
  have oldContacts := contacts firstIndex secondIndex firstCell secondCell firstValid' secondValid' different
    (GridPolyline.inverseAffineRealPoint factor shift point)
    ((GridPolyline.realContains_affine_inverse _ nonzero shift point).mp firstContains)
    ((GridPolyline.realContains_affine_inverse _ nonzero shift point).mp secondContains)
  have firstEndpoint := oldContacts.1.affine factor shift
  have secondEndpoint := oldContacts.2.affine factor shift
  rw [GridPolyline.affine_inverse_point nonzero] at firstEndpoint secondEndpoint
  exact ⟨firstEndpoint,secondEndpoint⟩

end PeriodicGridDrawing
end LeanTrominoes
