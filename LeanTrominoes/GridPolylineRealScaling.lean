/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentRealScaling
import LeanTrominoes.PeriodicGridDrawingRealGeometry

/-! # Uniform scaling of real polyline images -/
namespace LeanTrominoes.GridPolyline

theorem realContains_scale (route : List Cell) {factor : Int} (nonzero : factor ≠ 0) (point : ℝ × ℝ) :
    RealContains (scalePolyline factor route) ((factor : ℝ)*point.1,(factor : ℝ)*point.2) ↔
      RealContains route point := by
  unfold RealContains
  rw [gridPolylineSegments_scalePolyline]
  constructor
  · rintro ⟨segment,member,contains⟩
    obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
    exact ⟨original,originalMember,(GridSegment.realContains_scale _ nonzero _).mp contains⟩
  · rintro ⟨segment,member,contains⟩
    exact ⟨segment.scale factor,List.mem_map.mpr ⟨segment,member,rfl⟩,
      (GridSegment.realContains_scale _ nonzero _).mpr contains⟩

theorem realContains_scale_inverse (route : List Cell) {factor : Int} (nonzero : factor ≠ 0) (point : ℝ × ℝ) :
    RealContains (scalePolyline factor route) point ↔
      RealContains route (point.1/(factor : ℝ),point.2/(factor : ℝ)) := by
  have realNonzero : (factor : ℝ) ≠ 0 := by exact_mod_cast nonzero
  simpa only [mul_div_cancel₀ _ realNonzero,Prod.mk.eta] using
    realContains_scale route nonzero (point.1/(factor : ℝ),point.2/(factor : ℝ))

end LeanTrominoes.GridPolyline
