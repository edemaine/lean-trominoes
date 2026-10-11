/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendFanGeometry
import LeanTrominoes.GridPolylineRealOpenScaling
import LeanTrominoes.OrthogonalPolylineScaling
import LeanTrominoes.OrthogonalPolylineSymmetries

/-! # Placing and scaling the assigned fans at integer vertex copies -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision PeriodicOrthocrossing

def fanAt {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (factor : Int) (raster : Nat) (center : Cell) (port : GraphPort (Vertex V)) : List Cell :=
  translatePolyline (Cell.scale ((raster : Int)*factor) center) (scalePolyline raster (fanRoute source drawing port))

theorem fanAt_head {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (factor : Int) (raster : Nat) (center : Cell) (port : GraphPort (Vertex V)) :
    (fanAt source drawing factor raster center port).head? = some (Cell.scale ((raster : Int)*factor) center) := by
  simp only [fanAt,translatePolyline,scalePolyline,List.head?_map,fanRoute_head,Option.map_some,Cell.scale,Cell.add]
  simp

theorem fanAt_last {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (factor : Int) (raster : Nat) (center : Cell) (port : GraphPort (Vertex V)) :
    (fanAt source drawing factor raster center port).getLast? =
      some (Cell.add (Cell.scale ((raster : Int)*factor) center) (Cell.scale raster (fanAnchor source drawing port))) := by
  simp only [fanAt,translatePolyline,scalePolyline,List.getLast?_map,fanRoute_last,Option.map_some]

theorem fanAt_orthogonal {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (factor : Int) {raster : Nat} (positive : 0 < raster)
    (center : Cell) {port : GraphPort (Vertex V)} (member : port ∈ allPorts (subdivisionGraph source drawing)) :
    OrthogonalPolyline (fanAt source drawing factor raster center port) :=
  ((fanRoute_orthogonal planar member).scalePolyline positive).translate _

theorem fanAt_simple {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (factor : Int) {raster : Nat} (positive : 0 < raster)
    (center : Cell) {port : GraphPort (Vertex V)} (member : port ∈ allPorts (subdivisionGraph source drawing)) :
    GridPolyline.IsRealOpenSimple (fanAt source drawing factor raster center port) :=
  ((fanRoute_simple planar member).scale (by exact_mod_cast positive.ne')).translate _

theorem fanAt_points_bounds {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (factor : Int) (raster : Nat) (center : Cell) (port : GraphPort (Vertex V)) :
    ∀ point ∈ fanAt source drawing factor raster center port,
      (raster : Int)*factor*center.1-5*raster ≤ point.1 ∧ point.1 ≤ (raster : Int)*factor*center.1+5*raster ∧
      (raster : Int)*factor*center.2-10*raster ≤ point.2 ∧ point.2 ≤ (raster : Int)*factor*center.2+10*raster := by
  intro point member
  obtain ⟨scaled,scaledMember,rfl⟩ := List.mem_map.mp member
  obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp scaledMember
  have bounds := fanRoute_bounds source drawing port original originalMember
  have nonnegative : (0 : Int) ≤ raster := by positivity
  simp only [Cell.add,Cell.scale]
  exact ⟨by nlinarith [mul_le_mul_of_nonneg_left bounds.1 nonnegative],
    by nlinarith [mul_le_mul_of_nonneg_left bounds.2.1 nonnegative],
    by nlinarith [mul_le_mul_of_nonneg_left bounds.2.2.1 nonnegative],
    by nlinarith [mul_le_mul_of_nonneg_left bounds.2.2.2 nonnegative]⟩

theorem fanAt_real_bounds {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (factor : Int) (raster : Nat) (center : Cell) (port : GraphPort (Vertex V)) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (fanAt source drawing factor raster center port) point) :
    |point.1-(raster : ℝ)*factor*center.1| ≤ 5*raster ∧ |point.2-(raster : ℝ)*factor*center.2| ≤ 10*raster := by
  have bounds := GridPolyline.realContains_bounds (fanAt_points_bounds source drawing factor raster center port) contains
  push_cast at bounds
  exact ⟨abs_le.mpr ⟨by linarith [bounds.1],by linarith [bounds.2.1]⟩,
    abs_le.mpr ⟨by linarith [bounds.2.2.1],by linarith [bounds.2.2.2]⟩⟩

theorem fanAt_contacts_same_position {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    {factor : Int} (spacing : 20 < factor) {raster : Nat} (positive : 0 < raster)
    {firstCenter secondCenter : Cell} (first second : GraphPort (Vertex V)) {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (fanAt source drawing factor raster firstCenter first) point)
    (secondContains : GridPolyline.RealContains (fanAt source drawing factor raster secondCenter second) point) :
    firstCenter = secondCenter := by
  have firstBounds := fanAt_real_bounds source drawing factor raster firstCenter first firstContains
  have secondBounds := fanAt_real_bounds source drawing factor raster secondCenter second secondContains
  have rasterPositive : (0 : Int) < raster := by exact_mod_cast positive
  apply Prod.ext
  · apply GridSegment.closed_interval_periodic_shifts_unique (period := (raster : Int)*factor)
      (lower := -5*raster) (upper := 5*raster) (point := point.1) (by nlinarith) (by nlinarith)
    · push_cast
      exact ⟨by linarith [(abs_le.mp firstBounds.1).1],by linarith [(abs_le.mp firstBounds.1).2]⟩
    · push_cast
      exact ⟨by linarith [(abs_le.mp secondBounds.1).1],by linarith [(abs_le.mp secondBounds.1).2]⟩
  · apply GridSegment.closed_interval_periodic_shifts_unique (period := (raster : Int)*factor)
      (lower := -10*raster) (upper := 10*raster) (point := point.2) (by nlinarith) (by nlinarith)
    · push_cast
      exact ⟨by linarith [(abs_le.mp firstBounds.2).1],by linarith [(abs_le.mp firstBounds.2).2]⟩
    · push_cast
      exact ⟨by linarith [(abs_le.mp secondBounds.2).1],by linarith [(abs_le.mp secondBounds.2).2]⟩

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
